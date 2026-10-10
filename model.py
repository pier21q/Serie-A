"""Serie A Live - analisi e pronostici.

Qui sta tutto il calcolo statistico, usato sia dalla pagina sia dallo storico:
  - metriche di squadra, classifiche interne e stile di gioco
  - giocatori su cui ogni squadra fa affidamento
  - forza di attacco e difesa, con la stagione scorsa come base di partenza
  - pronostico della partita (Poisson con correzione Dixon-Coles) corretto per forma,
    accoppiamenti tattici, assenti e formazioni
  - proiezioni per giocatore: minuti, tiri, falli fatti e subiti, ammonizione, gol, assist
    e duello diretto con l'avversario
  - storico dei pronostici e verifica con i risultati
"""
import math
import re
import time
import unicodedata

K_PRIOR = 12           # peso della stagione scorsa sulle squadre, in partite equivalenti (un buon inizio conta, ma poco)
K_PRIOR_NEW = 6        # con un allenatore nuovo la stagione scorsa pesa meno
SOFT_CAP = .10         # tetto complessivo di forma, accoppiamenti tattici, stili e ritmo sui gol attesi
GOAL_SHARE_CAP, ASSIST_SHARE_CAP = .40, .30   # quota massima dei gol e degli assist dei titolari per un giocatore
# taratura degli attaccanti titolari sulle partite reali (confronto del 28/09/2026 su 50 partite)
LEAGUE = "Serie A"   # nome della lega nei testi: lo imposta server.py (SERIEA_LEGA)
# correzioni per ruolo: quota reale di ogni ruolo tra i titolari (430 partite ESPN della lega) diviso quella del
# modello, {statistica: {ruolo: fattore}}; le imposta server.py per ogni lega. Le squadre restano sui loro totali.
ROLE_CALIB = {}
F_CALIB = {"shots": .9, "sot": .87, "fouls": .85, "fouled": .88, "lamG": .85, "lamA": .65}
STYLE_EFF_CAP, TEMPO_CAP, CARDS_CAP = .06, .08, .2   # tetti degli effetti dello scontro di stili
EVID_K, EVID_CAP = 30, .05                            # precedenti tra stili: peso del campione e tetto
K_LEAGUE = 40          # peso della stagione scorsa sulle medie di campionato, in partite
PLAYER_PRIOR_MIN = 450  # peso del dato di base nelle statistiche per 90' dei giocatori, in minuti
RARE_PRIOR_MIN = 1200   # per gol, assist, xG e xA (eventi rari): circa 13 partite
RARE_KEYS = {"goals", "assists", "expectedGoals", "expectedAssists"}
RHO = -0.08            # correzione Dixon-Coles
CALIB = 0.80           # le forze di attacco e difesa vengono avvicinate un po' alla media (evita pronostici troppo netti)
FORM_EFF = 0.05        # effetto massimo della forma recente sui gol attesi
PAIR_ADV, PAIR_NEUT, PAIR_CAP = .03, -.02, .08   # accoppiamenti tattici: effetto per vantaggio, per neutralizzazione, tetto
MAXG = 10
NO_PRIOR = {"att": 1.0, "de": 1.0}


# ---------- utilità ----------

def num(x):
    if isinstance(x, bool) or not isinstance(x, (int, float)):
        return None
    return float(x) if math.isfinite(x) else None


def g(s, k):
    return num((s or {}).get(k))


def dv(a, b, mult=1.0):
    return a / b * mult if a is not None and b else None


def clamp(v, a, b):
    return max(a, min(b, v))


def mean(xs):
    xs = [x for x in xs if x is not None]
    return sum(xs) / len(xs) if xs else None


def fmt(v, d=1):
    if v is None:
        return "–"
    s = f"{v:,.{d}f}"
    return s.replace(",", "X").replace(".", ",").replace("X", ".")


def pm(k):
    return lambda s, n, c: dv(g(s, k), n)


def ratio(k1, k2):
    return lambda s, n, c: dv(g(s, k1), g(s, k2), 100)


def plain(k):
    return lambda s, n, c: g(s, k)


def _form(s, n, c):
    f = c["form"][:5]
    return sum(3 if r["r"] == "V" else 1 if r["r"] == "N" else 0 for r in f) / len(f) if f else None


def _venue(key):
    def f(s, n, c):
        r = c.get(key)
        return r["pts"] / r["p"] if r and r.get("p") else None
    return f


def _card(s, n, c):
    y = g(s, "yellowCards")
    if y is None:
        return None
    return dv(y + 2 * ((g(s, "yellowRedCards") or 0) + (g(s, "redCards") or 0)), n)


# hi: 1 = più alto è meglio, 0 = più basso è meglio, None = caratteristica di stile (né buona né cattiva)
METRICS = [
    dict(k="gpm", c="Attacco", l="Gol segnati", u="/p", d=2, hi=1, f=pm("goalsScored"), S="Attacco prolifico", W="Fatica a segnare"),
    dict(k="xg", c="Attacco", l="Expected goals (xG)", u="/p", d=2, hi=1, f=pm("expectedGoals"), S="Crea tanto (xG alto)", W="Produce poco (xG basso)"),
    dict(k="sot", c="Attacco", l="Tiri in porta", u="/p", d=1, hi=1, f=pm("shotsOnTarget"), S="Tanti tiri nello specchio", W="Pochi tiri nello specchio"),
    dict(k="bc", c="Attacco", l="Palloni giocati vicino all'area avversaria (deep)", sh="Palloni vicino all'area", u="/p", d=1, hi=1,
         f=pm("deep"), S="Arriva spesso vicino all'area", W="Arriva poco vicino all'area"),
    dict(k="conv", c="Attacco", l="Conversione tiri in gol", u="%", d=1, hi=1, f=ratio("goalsScored", "shots"), S="Cinica sotto porta", W="Spreca molto sotto porta"),
    dict(k="corners", c="Attacco", l="Calci d'angolo", u="/p", d=1, hi=1, f=pm("corners"), S="Tanti calci d'angolo", W="Pochi calci d'angolo"),
    dict(k="headed", c="Attacco", l="Gol di testa", u="/p", d=2, hi=1, f=pm("headedGoals"), S="Pericolosa di testa", W="Poco pericolosa di testa"),
    dict(k="poss", c="Costruzione", l="Possesso palla", u="%", d=1, hi=1, f=plain("averageBallPossession"), S="Domina il possesso", W="Lascia il pallone agli avversari"),
    dict(k="pass", c="Costruzione", l="Precisione passaggi", u="%", d=1, hi=1, f=plain("accuratePassesPercentage"), S="Palleggio preciso", W="Imprecisa in costruzione"),
    dict(k="kp", c="Costruzione", l="Passaggi chiave", u="/p", d=1, hi=1, f=pm("keyPasses"), S="Rifinitura di qualità", W="Poca rifinitura"),
    dict(k="cross", c="Costruzione", l="Cross riusciti", u="/p", d=1, hi=1, f=pm("accurateCrosses"), S="Pericolosa con i cross", W="Cross poco efficaci"),
    dict(k="gapm", c="Difesa", l="Gol subiti", u="/p", d=2, hi=0, f=pm("goalsConceded"), S="Difesa solida", W="Difesa perforabile"),
    dict(k="xga", c="Difesa", l="Expected goals concessi (xGA)", sh="xG concessi", u="/p", d=2, hi=0, f=pm("expectedGoalsAgainst"),
         S="Concede poche occasioni (xG concessi bassi)", W="Concede tante occasioni (xG concessi alti)"),
    dict(k="shA", c="Difesa", l="Tiri concessi", u="/p", d=1, hi=0, f=pm("shotsAgainst"), S="Concede pochi tiri", W="Subisce molti tiri"),
    dict(k="sotA", c="Difesa", l="Tiri in porta concessi", u="/p", d=1, hi=0, f=pm("shotsOnTargetAgainst"), S="Concede pochi tiri in porta", W="Concede molti tiri in porta"),
    dict(k="bcA", c="Difesa", l="Palloni concessi vicino alla propria area (deep)", sh="Palloni concessi vicino all'area", u="/p", d=1, hi=0,
         f=pm("deepAllowed"), S="Tiene gli avversari lontani dall'area", W="Lascia arrivare gli avversari vicino all'area"),
    dict(k="crossA", c="Difesa", l="Cross riusciti concessi", u="/p", d=1, hi=0, f=pm("crossesSuccessfulAgainst"), S="Chiude bene le fasce", W="Soffre i cross"),
    dict(k="cs", c="Difesa", l="Partite a porta inviolata", u="%", d=0, hi=1, f=lambda s, n, c: dv(g(s, "cleanSheets"), n, 100), S="Spesso a porta inviolata", W="Quasi mai a porta inviolata"),
    dict(k="gkp", c="Difesa", l="Parate sui tiri in porta subiti", sh="Parate (%)", u="%", d=0, hi=1,
         f=lambda s, n, c: dv(g(s, "saves"), g(s, "shotsOnTargetAgainst"), 100), S="Portiere decisivo", W="Portiere in difficoltà"),
    dict(k="rec", c="Difesa", l="Contrasti vinti", u="/p", d=1, hi=1, f=pm("tacklesWon"), S="Vince tanti contrasti", W="Vince pochi contrasti"),
    dict(k="int", c="Difesa", l="Intercetti", u="/p", d=1, hi=1, f=pm("interceptions"), S="Legge bene le linee di passaggio", W="Pochi intercetti"),
    dict(k="duel", c="Duelli e disciplina", l="Contrasti vinti sul totale", sh="Contrasti vinti (%)", u="%", d=1, hi=1, f=ratio("tacklesWon", "tackles"),
         S="Vince i contrasti", W="Perde i contrasti"),
    dict(k="air", c="Duelli e disciplina", l="Gol di testa subiti", u="/p", d=2, hi=0, f=pm("headedGoalsAgainst"),
         S="Solida sui palloni alti", W="Soffre i colpi di testa"),
    dict(k="foul", c="Duelli e disciplina", l="Falli commessi", u="/p", d=1, hi=0, f=pm("fouls"), S="Gioco pulito", W="Commette molti falli"),
    dict(k="card", c="Duelli e disciplina", l="Cartellini", u="/p", d=1, hi=0, f=_card, S="Disciplinata", W="Indisciplinata (cartellini)"),
    dict(k="form", c="Rendimento", l="Forma: punti/partita ultime 5", sh="Forma (ultime 5)", u="", d=2, hi=1, f=_form, S="In gran forma", W="Momento negativo"),
    dict(k="home", c="Rendimento", l="Punti/partita in casa", u="", d=2, hi=1, f=_venue("home"), S="Fortino in casa", W="Fragile in casa"),
    dict(k="away", c="Rendimento", l="Punti/partita in trasferta", u="", d=2, hi=1, f=_venue("away"), S="Rende bene in trasferta", W="Fatica in trasferta"),
    dict(k="long", c="Stile", l="Quota di lanci lunghi sul totale dei passaggi", sh="Quota lanci lunghi", u="%", d=1, hi=None, f=ratio("totalLongBalls", "totalPasses")),
    dict(k="press", c="Stile", l="PPDA: passaggi lasciati agli avversari per ogni azione difensiva (più basso = più pressing)", sh="PPDA (pressing)",
         u="", d=1, hi=None, f=plain("ppda")),
    dict(k="fk", c="Stile", l="Falli subiti (punizioni a favore)", sh="Falli subiti", u="/p", d=1, hi=None, f=pm("freeKicks")),
    dict(k="territory", c="Stile", l="Quota dei palloni giocati vicino alle aree che sono suoi", sh="Baricentro (vicino all'area)", u="%", d=0,
         hi=None, f=lambda s, n, c: dv(g(s, "deep"), (g(s, "deep") or 0) + (g(s, "deepAllowed") or 0), 100) if g(s, "deep") is not None else None),
    dict(k="tempo", c="Stile", l="Tiri totali in partita (fatti e subiti)", sh="Ritmo (tiri totali)", u="/p", d=1, hi=None,
         f=lambda s, n, c: dv(g(s, "shots") + (g(s, "shotsAgainst") or 0), n) if g(s, "shots") is not None else None),
]
MK = {m["k"]: m for m in METRICS}


def mval(k, v):
    m = MK[k]
    return fmt(v, m["d"]) + ("%" if m["u"] == "%" else "")


def munit(k):
    return " a partita" if MK[k]["u"] == "/p" else ""


def metrics_meta():
    return [{k: v for k, v in m.items() if k != "f"} for m in METRICS]


# ---------- squadre ----------

def team_forms(played):
    form = {}
    for e in sorted(played or [], key=lambda e: -(e.get("start") or 0)):
        if e.get("hs") is None or e.get("as") is None:
            continue
        for home, t, o in ((True, e["home"], e["away"]), (False, e["away"], e["home"])):
            gf, ga = (e["hs"], e["as"]) if home else (e["as"], e["hs"])
            form.setdefault(str(t["id"]), []).append({
                "r": "V" if gf > ga else "P" if gf < ga else "N", "gf": gf, "ga": ga,
                "opp": o, "home": home, "start": e["start"], "id": e["id"]})
    return form


def team_metrics(stats, n, ctx):
    out = {}
    for M in METRICS:
        try:
            v = M["f"](stats, n, ctx)
        except Exception:
            v = None
        out[M["k"]] = v if v is not None and math.isfinite(v) else None
    return out


def rank_all(teams_m):
    rank = {t: {} for t in teams_m}
    pct = {t: {} for t in teams_m}
    z = {t: {} for t in teams_m}
    for M in METRICS:
        k = M["k"]
        sign = -1 if M["hi"] == 0 else 1
        vals = [(t, m[k]) for t, m in teams_m.items() if m.get(k) is not None]
        if not vals:
            continue
        arr = [v for _, v in vals]
        mu = sum(arr) / len(arr)
        sd = math.sqrt(sum((x - mu) ** 2 for x in arr) / len(arr)) or 1
        for t, v in vals:
            better = sum(1 for _, o in vals if (o - v) * sign > 1e-9)
            worse = sum(1 for _, o in vals if (v - o) * sign > 1e-9)
            rank[t][k] = better + 1
            pct[t][k] = (worse + (len(vals) - 1 - better - worse) / 2) / (len(vals) - 1) if len(vals) > 1 else .5
            z[t][k] = (v - mu) / sd * sign
    return rank, pct, z


def league_block(standings, teams_m):
    home = standings.get("home") or []
    hp = sum(r["p"] for r in home)
    col = lambda k: mean([m.get(k) for m in teams_m.values()])
    yellow = mean([dv(g(s, "yellowCards"), n) for s, n in teams_m.get("_raw", [])]) if "_raw" in teams_m else None
    return {
        "hp": hp, "hgf": sum(r["gf"] for r in home), "hga": sum(r["ga"] for r in home),
        "sotA": col("sotA"), "bcA": col("bcA"), "shA": col("shA"), "fk": col("fk"), "foul": col("foul"),
        "xg": col("xg"), "gpm": col("gpm"), "yellow": yellow,
    }


def rating(m, L):
    mu = L["mu"]
    gpm = m.get("gpm") if m.get("gpm") is not None else mu
    xg = m.get("xg") if m.get("xg") is not None else gpm
    gapm = m.get("gapm") if m.get("gapm") is not None else mu
    sotA = m.get("sotA") if m.get("sotA") is not None else L["sotA"]
    bcA = m.get("bcA") if m.get("bcA") is not None else L["bcA"]
    att = (.55 * gpm + .45 * xg) / mu
    de = .55 * gapm / mu + .45 * (.5 * sotA / L["sotA"] + .5 * bcA / L["bcA"])
    return {"att": att, "de": de, "xg": xg}


# ---------- stile di gioco e giocatori chiave ----------

def style_tags(m, pct, rank):
    P = lambda k: pct.get(k)
    R = lambda k: rank.get(k)
    tags = []

    def add(cond, title, why, score):
        if cond:
            tags.append({"t": title, "why": why, "s": round(score, 3)})

    ok = lambda *ks: all(P(k) is not None for k in ks)
    if ok("poss", "pass"):
        add(P("poss") >= .75 and P("pass") >= .55, "Possesso palleggiato",
            f"{mval('poss', m['poss'])} di possesso ({R('poss')}ª), {mval('pass', m['pass'])} di passaggi riusciti", P("poss"))
    if ok("long"):
        add(P("long") >= .75, "Gioco diretto con lanci lunghi",
            f"{mval('long', m['long'])} dei passaggi sono lanci lunghi ({R('long')}ª per quota)", P("long"))
    if ok("cross"):
        add(P("cross") >= .75, "Gioco sulle fasce e cross",
            f"{mval('cross', m['cross'])} cross riusciti a partita ({R('cross')}ª)", P("cross"))
    if ok("xg", "poss"):
        add(P("xg") >= .6 and P("poss") <= .35, "Pericolosa anche con poco pallone",
            f"{mval('xg', m['xg'])} xG a partita con il {mval('poss', m['poss'])} di possesso", (P("xg") + 1 - P("poss")) / 2)
    if ok("press"):
        add(P("press") <= .25, "Pressing alto",
            f"PPDA {mval('press', m['press'])}: gli avversari fanno pochi passaggi prima di subire un'azione difensiva ({R('press')}ª per PPDA)", 1 - P("press"))
    if ok("poss", "press"):
        add(P("poss") <= .3 and P("press") >= .7, "Blocco basso",
            f"poco possesso ({mval('poss', m['poss'])}) e lascia costruire gli avversari", 1 - P("poss"))
    if ok("corners", "headed"):
        add(P("corners") >= .7 and P("headed") >= .7, "Pericolosa su palla inattiva",
            f"{mval('corners', m['corners'])} angoli a partita, {mval('headed', m['headed'])} gol di testa a partita", (P("corners") + P("headed")) / 2)
    if ok("duel"):
        add(P("duel") >= .8, "Aggressiva nei contrasti",
            f"{mval('duel', m['duel'])} di contrasti vinti ({R('duel')}ª)", P("duel"))
    if ok("foul"):
        add(P("foul") <= .2, "Gioco spezzettato, molti falli",
            f"{mval('foul', m['foul'])} falli commessi a partita", 1 - P("foul"))
    return sorted(tags, key=lambda t: -t["s"])[:5]


def contrib(p):
    return .5 * ((p.get("expectedGoals") or 0) + (p.get("expectedAssists") or 0)) + .5 * ((p.get("goals") or 0) + (p.get("assists") or 0))


DEF_WEIGHT = {"G": 0.0, "D": 0.12, "M": 0.06, "F": 0.02}


def def_weight(p, avail):
    """Peso difensivo di un giocatore: minuti giocati e ruolo (le nuove fonti non danno contrasti per giocatore)."""
    return min(1.0, (p.get("minutesPlayed") or 0) / avail) * DEF_WEIGHT.get(p.get("pos") or "M", .06)


def reliance(tid, n, players):
    ps = [p for p in players if str(p.get("teamId")) == tid and (p.get("minutesPlayed") or 0) > 0]
    if not ps:
        return {"shares": {}}
    tot_c = sum(contrib(p) for p in ps) or 1
    tot_kp = sum(p.get("keyPasses") or 0 for p in ps) or 1
    avail = max(1, n) * 90
    tot_b = sum(p.get("xGBuildup") or 0 for p in ps) or 1
    shares = {}
    for p in ps:
        shares[p["id"]] = {
            "att": contrib(p) / tot_c, "kp": (p.get("keyPasses") or 0) / tot_kp,
            "def": def_weight(p, avail), "build": (p.get("xGBuildup") or 0) / tot_b,
            "min": (p.get("minutesPlayed") or 0) / avail, "pos": p.get("pos"),
        }
    card = lambda p, extra: {"id": p["id"], "name": p["name"], "pos": p.get("pos"), **extra}
    by = lambda key: sorted(ps, key=lambda p: -shares[p["id"]][key])
    attack = [card(p, {"share": shares[p["id"]]["att"], "g": p.get("goals") or 0, "a": p.get("assists") or 0,
                       "xg": p.get("expectedGoals"), "xa": p.get("expectedAssists")})
              for p in by("att")[:3] if shares[p["id"]]["att"] >= .08]
    creator = [card(p, {"share": shares[p["id"]]["kp"], "kp": p.get("keyPasses") or 0}) for p in by("kp")[:2] if shares[p["id"]]["kp"] >= .1]
    defense = [card(p, {"share": shares[p["id"]]["build"], "xgb": p.get("xGBuildup")}) for p in by("build")[:2] if shares[p["id"]]["build"] >= .1]
    always = [card(p, {"share": shares[p["id"]]["min"]}) for p in sorted(ps, key=lambda p: -(p.get("minutesPlayed") or 0))
              if shares[p["id"]]["min"] >= .9][:6]
    rated = sorted([p for p in ps if p.get("rating") and (p.get("ratingPV") or 0) >= max(2, .4 * n)], key=lambda p: -p["rating"])
    roles = {}
    for key, field in (("xg", "expectedGoals"), ("goals", "goals")):
        tot = sum(p.get(field) or 0 for p in ps)
        if tot:
            roles[key] = {pos: sum(p.get(field) or 0 for p in ps if p.get("pos") == pos) / tot for pos in ("D", "M", "F")}
    per90 = lambda p, k: (p.get(k) or 0) / p["minutesPlayed"] * 90
    enough = [p for p in ps if p.get("pos") != "G" and (p.get("minutesPlayed") or 0) >= 270]
    incl = {}
    for key, field, real in (("scorer", "expectedGoals", "goals"), ("assister", "expectedAssists", "assists")):
        best = max(enough, key=lambda p: per90(p, field) + .5 * per90(p, real), default=None)
        if best and (best.get(field) or best.get(real)):
            incl[key] = card(best, {"per90": per90(best, field), "real": best.get(real) or 0, "min": best["minutesPlayed"]})
    return {
        "attack": attack, "creator": creator, "defense": defense, "always": always, **incl,
        "best": card(rated[0], {"rating": rated[0]["rating"], "pv": rated[0].get("ratingPV")}) if rated else None,
        "roles": roles, "shares": shares,
    }


# ---------- ruoli valorizzati dall'allenatore ----------

ROLE_FAMILY = {"Difensore centrale": "Difensori centrali", "Terzino": "Terzini", "Esterno": "Esterni di fascia",
               "Mediano": "Mediani e registi", "Regista": "Mediani e registi", "Centrocampista": "Mediani e registi",
               "Mezzala": "Mezzali", "Trequartista": "Trequartisti", "Esterno offensivo": "Ali ed esterni offensivi",
               "Ala": "Ali ed esterni offensivi", "Centravanti": "Attaccanti", "Attaccante": "Attaccanti"}
FAMILIES = ["Attaccanti", "Ali ed esterni offensivi", "Trequartisti", "Mezzali", "Mediani e registi",
            "Esterni di fascia", "Terzini", "Difensori centrali"]
K_ROLE = 3.0   # gol (o assist) "di base" per ruolo: con pochi dati l'indice resta vicino a 1


def coach_key(name):
    return " ".join(sorted(norm_tokens(name))) if name else None


def role_agg(rows):
    a = {"n": 0, "slots": {}, "g": {}, "a": {}, "G": 0, "A": 0, "S": 0, "teams": {}}
    for r in rows:
        a["n"] += 1
        lab = (r.get("team"), r.get("season"))
        a["teams"][lab] = a["teams"].get(lab, 0) + 1
        for f, k in (r.get("slots") or {}).items():
            a["slots"][f] = a["slots"].get(f, 0) + k
            a["S"] += k
        for key, big in (("g", "G"), ("a", "A")):
            for f in r.get(key) or []:
                if f in FAMILIES:
                    a[key][f] = a[key].get(f, 0) + 1
                    a[big] += 1
    return a


def role_profile(rows, league, prior_year=None):
    """Da dove arrivano gol e assist con un allenatore, ruolo per ruolo, e quanto ogni ruolo rende rispetto
    alla media della Serie A per quel ruolo (a parità di quanti giocatori schiera in quel ruolo e di quanto segna
    la squadra): indice 1 = come la media, 1,5 = il 50% in più."""
    c = role_agg(rows)
    if not c["n"] or not c["S"] or not league["S"]:
        return None
    rel_g = (c["G"] / c["S"]) / (league["G"] / league["S"]) if league["G"] else 1
    rel_a = (c["A"] / c["S"]) / (league["A"] / league["S"]) if league["A"] else 1
    roles = []
    for f in FAMILIES:
        sl, g, a = c["slots"].get(f, 0), c["g"].get(f, 0), c["a"].get(f, 0)
        if not sl and not g and not a:
            continue
        ls = league["slots"].get(f) or 0
        exp_g = sl * (league["g"].get(f, 0) / ls if ls else 0) * rel_g
        exp_a = sl * (league["a"].get(f, 0) / ls if ls else 0) * rel_a
        roles.append({"f": f, "per": sl / c["n"], "g": g, "a": a,
                      "gShare": g / c["G"] if c["G"] else 0, "aShare": a / c["A"] if c["A"] else 0,
                      "gIdx": clamp((g + K_ROLE) / (exp_g + K_ROLE), .5, 2), "aIdx": clamp((a + K_ROLE) / (exp_a + K_ROLE), .5, 2),
                      "lgShareG": league["g"].get(f, 0) / league["G"] if league["G"] else 0,
                      "lgShareA": league["a"].get(f, 0) / league["A"] if league["A"] else 0})
    teams = [{"team": t, "season": "cur" if se == "cur" else prior_year or "scorsa", "n": k}
             for (t, se), k in sorted(c["teams"].items(), key=lambda kv: (kv[0][1] != "cur", -kv[1]))]
    return {"n": c["n"], "G": c["G"], "A": c["A"], "roles": roles, "teams": teams}


def role_text(name, prof):
    """Una frase: da dove arrivano gol e assist con questo allenatore e quali ruoli rendono più della media."""
    if not prof or not prof["roles"] or not prof["G"]:
        return None
    low = lambda f: f[0].lower() + f[1:]
    tg = max(prof["roles"], key=lambda r: r["gShare"])
    ta = max(prof["roles"], key=lambda r: r["aShare"])
    txt = f"Con {name} i gol arrivano soprattutto da {low(tg['f'])} ({round(tg['gShare'] * 100)}%)"
    txt += f", gli assist da {low(ta['f'])} ({round(ta['aShare'] * 100)}%)." if prof["A"] else "."
    up = [r for r in prof["roles"] if max(r["gIdx"], r["aIdx"]) >= 1.3 and r["g"] + r["a"] >= 3]
    if up:
        parts = [f"{low(r['f'])} ({'gol' if r['gIdx'] >= r['aIdx'] else 'assist'} ×{max(r['gIdx'], r['aIdx']):.1f})".replace(".", ",")
                 for r in sorted(up, key=lambda r: -max(r["gIdx"], r["aIdx"]))[:2]]
        txt += f" Rendono più della media del loro ruolo in {LEAGUE}: " + " e ".join(parts) + "."
    if prof["n"] < 8:
        txt += f" Pochi dati ({prof['n']} partit{'a' if prof['n'] == 1 else 'e'}): pesa poco nel pronostico."
    return txt


def formations_of(tid, matches):
    count, last = {}, None
    for eid, x in sorted(matches.items(), key=lambda kv: -(kv[1].get("start") or 0)):
        lu = x.get("lineups")
        if not x.get("final") or not lu:
            continue
        side = "home" if str(x.get("homeId")) == tid else "away" if str(x.get("awayId")) == tid else None
        if not side:
            continue
        s = lu.get(side) or {}
        if s.get("formation"):
            count[s["formation"]] = count.get(s["formation"], 0) + 1
        if last is None and len(s.get("starters") or []) >= 11:
            last = {"formation": s.get("formation"), "starters": s["starters"], "start": x.get("start")}
    return count, last


# ---------- identità tattica: stile di gioco, allenatore, scontro di stili ----------

STYLE_LABELS = [("possesso", "Possesso"), ("baricentro", "Baricentro alto"), ("pressing", "Pressing"),
                ("verticalita", "Gioco verticale"), ("ampiezza", "Ampiezza e cross"), ("transizioni", "Transizioni"),
                ("fisicita", "Fisicità e duelli"), ("ritmo", "Ritmo (tiri totali)")]


def style_dims(pct):
    """Otto dimensioni di stile, da 0 a 1 (posizione rispetto alle altre squadre)."""
    def P(k):
        v = pct.get(k)
        return .5 if v is None else v
    return {
        "possesso": (2 * P("poss") + P("pass")) / 3,
        "baricentro": P("territory"),
        "pressing": (2 * (1 - P("press")) + P("rec")) / 3,
        "verticalita": (2 * P("long") + (1 - P("pass"))) / 3,
        "ampiezza": (2 * P("cross") + P("corners")) / 3,
        "transizioni": ((1 - P("poss")) + P("xg")) / 2,   # pericolosa (xG) pur tenendo poco il pallone
        "fisicita": (P("duel") + P("air") + (1 - P("foul"))) / 3,
        "ritmo": P("tempo"),
    }


ARCHETYPES = [
    ("palleggio", "Palleggio e controllo", lambda s: (2 * s["possesso"] + s["baricentro"]) / 3,
     "vuole il pallone, costruisce con pazienza e gioca nella metà campo avversaria"),
    ("pressing", "Pressing alto e aggressione", lambda s: (2 * s["pressing"] + s["baricentro"]) / 3,
     "va a prendere gli avversari in alto e prova a recuperare palla vicino alla loro porta"),
    ("blocco", "Blocco basso e ripartenze", lambda s: ((1 - s["possesso"]) + s["transizioni"] + (1 - s["baricentro"])) / 3,
     "difende compatta e bassa, lascia il pallone agli avversari e riparte in velocità"),
    ("diretto", "Gioco diretto e fisico", lambda s: (s["verticalita"] + s["fisicita"]) / 2,
     "cerca presto la profondità con i lanci lunghi e vince i duelli"),
    ("ampiezza", "Ampiezza e cross", lambda s: s["ampiezza"],
     "allarga il gioco sugli esterni e cerca l'area con i cross"),
]


def archetype(dims):
    scored = sorted(((f(dims), key, name, desc) for key, name, f, desc in ARCHETYPES), reverse=True)
    top = scored[0]
    if top[0] < .6:
        return {"key": "equilibrio", "name": "Squadra equilibrata", "score": round(top[0], 3), "second": None,
                "desc": "non ha un tratto dominante e adatta il gioco all'avversario"}
    second = scored[1] if scored[1][0] >= .6 else None
    return {"key": top[1], "name": top[2], "desc": top[3], "score": round(top[0], 3),
            "second": {"key": second[1], "name": second[2]} if second else None}


def style_summary(t):
    m, a, c = t["m"], t["arch"], t.get("coach")
    lead = f"Con {c['name']} la squadra" if c and c.get("name") else "La squadra"
    bits = []
    if m.get("poss") is not None:
        bits.append(f"{mval('poss', m['poss'])} di possesso")
    if m.get("long") is not None:
        bits.append(f"{mval('long', m['long'])} dei passaggi in lancio lungo")
    if m.get("territory") is not None:
        bits.append(f"{mval('territory', m['territory'])} dei palloni giocati vicino alle aree sono suoi")
    if m.get("press") is not None:
        bits.append(f"PPDA {mval('press', m['press'])}")
    if m.get("cross") is not None:
        bits.append(f"{mval('cross', m['cross'])} cross riusciti a partita")
    return f"{lead} {a['desc']}." + (f" In numeri: {', '.join(bits)}." if bits else "")


def style_changes(cur, prev):
    if not prev:
        return []
    out = []
    for k, label in STYLE_LABELS:
        d = cur[k] - prev[k]
        if abs(d) >= .2:
            out.append({"k": k, "label": label, "from": round(prev[k], 2), "to": round(cur[k], 2)})
    return sorted(out, key=lambda x: -abs(x["to"] - x["from"]))


def coach_profile(tid, coaches, season_start):
    """Allenatore della squadra e rendimento nelle sue ultime partite (anche con squadre precedenti)."""
    c = (coaches or {}).get(tid) or {}
    m = c.get("manager")
    if not m:
        return None
    det = c.get("detail") or {}
    evs = [e for e in c.get("events") or [] if e.get("hs") is not None]
    freq = {}
    for e in evs:
        for side in ("home", "away"):
            freq[e[side]["id"]] = freq.get(e[side]["id"], 0) + 1
    rec = {"n": 0, "w": 0, "d": 0, "l": 0, "gf": 0, "ga": 0, "over": 0, "cs": 0}
    teams, same = {}, None
    for e in evs:
        mine = "home" if freq.get(e["home"]["id"], 0) >= freq.get(e["away"]["id"], 0) else "away"
        gf, ga = (e["hs"], e["as"]) if mine == "home" else (e["as"], e["hs"])
        rec["n"] += 1
        rec["w" if gf > ga else "d" if gf == ga else "l"] += 1
        rec["gf"] += gf
        rec["ga"] += ga
        rec["over"] += gf + ga > 2
        rec["cs"] += ga == 0
        teams[e[mine]["name"]] = teams.get(e[mine]["name"], 0) + 1
        if season_start and e["start"] < season_start and str(e[mine]["id"]) == tid:
            same = True
    if same is None and season_start and evs and min(e["start"] for e in evs) < season_start:
        same = False   # ha partite prima di questa stagione, ma non con questa squadra: allenatore nuovo
    if same is None and (c.get("wiki") or {}).get("new") is not None:
        same = not c["wiki"]["new"]   # da Wikipedia: allenatore della scorsa stagione diverso o uguale
    age = int((time.time() - det["dob"]) / 31557600) if det.get("dob") else None
    return {"id": m.get("id"), "name": m.get("name"), "formation": det.get("formation"), "country": det.get("country"),
            "age": age, "performance": det.get("performance"), "record": rec,
            "teams": sorted(teams.items(), key=lambda kv: -kv[1]), "same": same}


def arch_table(entries):
    """Risultati per coppia di stili: (stile, stile avversario) e (stile, tutti)."""
    tab = {}
    for ah, aa, hs, as_ in entries:
        for me, opp, gf, ga in ((ah, aa, hs, as_), (aa, ah, as_, hs)):
            pts = 3 if gf > ga else 1 if gf == ga else 0
            for key in ((me, opp), (me, None)):
                r = tab.setdefault(key, {"n": 0, "gf": 0, "ga": 0, "pts": 0})
                r["n"] += 1
                r["gf"] += gf
                r["ga"] += ga
                r["pts"] += pts
    return tab


def style_clash(H, Aw, A):
    """Come si scontrano gli stili: regole tattiche e precedenti tra squadre con gli stessi stili."""
    items, eff, tot = [], {"h": 0.0, "a": 0.0}, {"tempo": 0.0, "cards": 0.0, "poss": 0.0}
    names = {"h": H["team"]["name"], "a": Aw["team"]["name"]}
    ids = {"h": H["id"], "a": Aw["id"]}

    def add(title, text, side=None, e=0.0, tempo=0.0, cards=0.0, poss=0.0, kind="rule"):
        if side:
            eff[side] += e
        tot["tempo"] += tempo
        tot["cards"] += cards
        tot["poss"] += poss if side != "a" else -poss
        chips = []
        if side and e:
            chips.append(f"gol attesi {names[side]} {'+' if e > 0 else ''}{fmt(e * 100, 0)}%")
        if tempo:
            chips.append(f"ritmo {'+' if tempo > 0 else ''}{fmt(tempo * 100, 0)}%")
        if cards:
            chips.append(f"cartellini +{fmt(cards * 100, 0)}%")
        items.append({"title": title, "text": text, "winner": ids[side] if side and e > 0 else ids["a" if side == "h" else "h"] if side and e < 0 else None,
                      "chips": chips, "kind": kind})

    for side, other, X, Y in (("h", "a", H, Aw), ("a", "h", Aw, H)):
        x, y, xn, yn = X["dims"], Y["dims"], names[side], names[other]
        if x["possesso"] >= .65 and y["pressing"] >= .65:
            sec, acc = X["pct"].get("pass"), X["m"].get("pass")
            acc_txt = f" ({mval('pass', acc)} di passaggi riusciti)" if acc is not None else ""
            if sec is not None and sec >= .55:
                add("Palleggio contro pressing alto", f"{xn} costruisce dal basso con passaggi precisi{acc_txt}: se supera la prima pressione di {yn} trova campo aperto.", side, .04, cards=.06)
            elif sec is not None:
                add("Palleggio contro pressing alto", f"{xn} vuole costruire dal basso ma sbaglia parecchi passaggi{acc_txt}: il pressing alto di {yn} può recuperare palloni vicino alla porta.", other, .04, cards=.06)
        if x["possesso"] >= .65 and y["possesso"] <= .4 and y["baricentro"] <= .45:
            tools = max(X["pct"].get("kp") or 0, x["ampiezza"])
            if tools >= .65:
                add("Possesso contro blocco basso", f"{xn} avrà il pallone contro il blocco basso di {yn} e ha gli strumenti per scardinarlo: rifinitura e cross.", side, .02, tempo=-.03, poss=4)
            else:
                add("Possesso contro blocco basso", f"{xn} avrà il pallone ma rischia di farlo girare senza trovare spazi contro il blocco basso di {yn}.", side, -.03, tempo=-.04, poss=4)
            if y["transizioni"] >= .6:
                add("Ripartenze contro squadra sbilanciata", f"{yn} aspetta e riparte: con {xn} spinta in avanti, le ripartenze possono fare male.", other, .03)
        if x["verticalita"] >= .65:
            ya = Y["pct"].get("air")
            if ya is not None and ya <= .35:
                add("Lanci lunghi contro difesa debole di testa", f"{xn} cerca spesso la profondità con i lanci lunghi e {yn} soffre nel gioco aereo.", side, .04)
            elif ya is not None and ya >= .7:
                add("Lanci lunghi contro difesa forte di testa", f"I lanci lunghi di {xn} trovano una difesa, quella di {yn}, che vince molti duelli aerei.", side, -.03)
        if x["ampiezza"] >= .65:
            yc = Y["pct"].get("crossA")
            if yc is not None and yc <= .35:
                add("Gioco sulle fasce contro difesa che soffre i cross", f"{xn} allarga il gioco e crossa molto, {yn} concede tanti cross riusciti.", side, .03)
            elif yc is not None and yc >= .7:
                add("Gioco sulle fasce contro difesa che chiude le fasce", f"{xn} vive di cross, ma {yn} chiude bene gli esterni.", side, -.02)
        if x["transizioni"] >= .65 and y["baricentro"] >= .65:
            add("Transizioni contro difesa alta", f"{xn} è pericolosa in ripartenza e {yn} gioca con la squadra alta: ci sarà spazio alle spalle della difesa.", side, .04)
        if x["fisicita"] >= .7 and y["possesso"] >= .6 and y["fisicita"] <= .4:
            add("Fisicità contro tecnica", f"{xn} alzerà l'intensità dei duelli contro una squadra più tecnica come {yn}.", side, .02, cards=.06)

    h, a = H["dims"], Aw["dims"]
    if h["pressing"] >= .6 and a["pressing"] >= .6:
        add("Pressing contro pressing", "Entrambe vanno a prendere gli avversari alti: partita spezzata, intensa, con molti duelli e falli.", tempo=.04, cards=.12)
    if h["possesso"] <= .4 and a["possesso"] <= .4:
        add("Due squadre che aspettano", "Nessuna delle due ama tenere il pallone: pochi spazi e partita bloccata.", tempo=-.08)
    if h["possesso"] >= .65 and a["possesso"] >= .65:
        better = "h" if (H["pct"].get("pass") or 0) >= (Aw["pct"].get("pass") or 0) else "a"
        add("Sfida per il pallone", f"Tutte e due vogliono il possesso: il palleggio più preciso di {names[better]} può fare la differenza a centrocampo.", better, .02)
    if h["ritmo"] >= .7 and a["ritmo"] >= .7:
        add("Due squadre da partite aperte", "Entrambe giocano partite con tanti tiri, fatti e subiti.", tempo=.05)
    elif h["ritmo"] <= .3 and a["ritmo"] <= .3:
        add("Due squadre da partite chiuse", "Entrambe giocano partite con pochi tiri.", tempo=-.05)

    # precedenti: come sono andate le partite tra squadre con questi due stili
    tab = A.get("archTable") or {}
    for side, other, X, Y in (("h", "a", H, Aw), ("a", "h", Aw, H)):
        r, base = tab.get((X["arch"]["key"], Y["arch"]["key"])), tab.get((X["arch"]["key"], None))
        if not r or not base or r["n"] < 6 or not base["gf"]:
            continue
        ratio_ = (r["gf"] / r["n"]) / (base["gf"] / base["n"])
        e = clamp(r["n"] / (r["n"] + EVID_K) * (ratio_ - 1), -EVID_CAP, EVID_CAP)
        add(f"Precedenti: «{X['arch']['name']}» contro «{Y['arch']['name']}»",
            f"Nelle partite precedenti le squadre come {names[side]} contro squadre come {names[other]} hanno segnato "
            f"{fmt(r['gf'] / r['n'], 1)} gol e subito {fmt(r['ga'] / r['n'], 1)} a partita, con {fmt(r['pts'] / r['n'], 2)} punti "
            f"({r['n']} partite, contro una media di {fmt(base['gf'] / base['n'], 1)} gol fatti).",
            side if abs(e) >= .01 else None, e if abs(e) >= .01 else 0.0, kind="evidence")

    eff = {k: clamp(v, -STYLE_EFF_CAP, STYLE_EFF_CAP) for k, v in eff.items()}
    return {"items": items, "eff": eff, "tempo": clamp(tot["tempo"], -TEMPO_CAP, TEMPO_CAP),
            "cards": clamp(tot["cards"], 0, CARDS_CAP), "poss": tot["poss"]}


# ---------- analisi complessiva ----------

def venue_tables(results):
    """Classifiche in casa e in trasferta calcolate dai risultati (ESPN dà solo quella generale)."""
    tab = {"home": {}, "away": {}}
    for e in results or []:
        if e.get("hs") is None or e.get("as") is None:
            continue
        for side, gf, ga in (("home", e["hs"], e["as"]), ("away", e["as"], e["hs"])):
            t = e[side]
            r = tab[side].setdefault(str(t["id"]), {"team": t, "p": 0, "w": 0, "d": 0, "l": 0, "gf": 0, "ga": 0, "pts": 0})
            r["p"] += 1
            r["gf"] += gf
            r["ga"] += ga
            r["w" if gf > ga else "d" if gf == ga else "l"] += 1
            r["pts"] += 3 if gf > ga else 1 if gf == ga else 0
    return {k: list(v.values()) for k, v in tab.items()}


def build(data, prior=None, matches=None, now=None, coaches=None, role_rows=None):
    now = now or time.time()
    matches = matches or {}
    st = data.get("standings") or {}
    # in casa e in trasferta: sempre dai risultati veri (le tabelle salvate non si aggiornano più)
    if data.get("played"):
        st = dict(st, **venue_tables(data["played"]))
    if prior and len([e for e in prior.get("results") or [] if e.get("hs") is not None]) >= 100:
        prior = dict(prior, standings=dict(prior.get("standings") or {}, **venue_tables(prior["results"])))
    rows = {k: {str(r["team"]["id"]): r for r in st.get(k) or []} for k in ("total", "home", "away")}
    forms = team_forms(data.get("played"))
    players = data.get("players") or []
    T = {}
    for tid, o in (data.get("teams") or {}).items():
        s = o.get("stats") or {}
        n = int(g(s, "matches") or (rows["total"].get(tid) or {}).get("p") or 0) or 1
        ctx = {"form": forms.get(tid, []), "home": rows["home"].get(tid), "away": rows["away"].get(tid)}
        T[tid] = {"id": int(tid), "team": o["team"], "n": n, "s": s, "ctx": ctx, "m": team_metrics(s, n, ctx)}
    rank, pct, z = rank_all({t: x["m"] for t, x in T.items()})

    # medie di campionato (stagione in corso, con la scorsa come base)
    cur = league_block(st, {t: x["m"] for t, x in T.items()})
    cur["yellow"] = mean([dv(g(x["s"], "yellowCards"), x["n"]) for x in T.values()])
    pr_league, pr_rating, pr_xg = None, {}, {}
    prev_dims, prev_arch = {}, {}
    if prior and prior.get("teams"):
        pst = prior.get("standings") or {}
        prow = {str(r["team"]["id"]): r for r in pst.get("total") or []}
        pm_ = {}
        for tid, s in prior["teams"].items():
            n = int(g(s, "matches") or (prow.get(tid) or {}).get("p") or 0) or 1
            pm_[tid] = team_metrics(s, n, {"form": [], "home": None, "away": None})
        pr_league = league_block(pst, pm_)
        pr_league["yellow"] = mean([dv(g(s, "yellowCards"), int(g(s, "matches") or 38)) for s in prior["teams"].values()])
        pr_league["mu"] = (pr_league["hgf"] + pr_league["hga"]) / (2 * pr_league["hp"]) if pr_league["hp"] else 1.3
        for tid, m in pm_.items():
            pr_rating[tid] = rating(m, pr_league)
        _, ppct, _ = rank_all(pm_)
        for tid in pm_:
            prev_dims[tid] = style_dims(ppct[tid])
            prev_arch[tid] = archetype(prev_dims[tid])["key"]
        # neopromosse: base = media delle ultime 5 della stagione scorsa
        bottom = [str(r["team"]["id"]) for r in sorted(pst.get("total") or [], key=lambda r: -r["pos"])[:5]]
        b = [pr_rating[t] for t in bottom if t in pr_rating]
        if b:
            pr_rating["_promoted"] = {k: mean([x[k] for x in b]) for k in ("att", "de", "xg")}

    HA_p = pr_league["hgf"] / pr_league["hp"] if pr_league and pr_league["hp"] else 1.45
    AA_p = pr_league["hga"] / pr_league["hp"] if pr_league and pr_league["hp"] else 1.15
    L = {
        "HA": (cur["hgf"] + HA_p * K_LEAGUE) / (cur["hp"] + K_LEAGUE),
        "AA": (cur["hga"] + AA_p * K_LEAGUE) / (cur["hp"] + K_LEAGUE),
        "N": len(T), "maxMin": max([p.get("minutesPlayed") or 0 for p in players] + [1]),
    }
    L["mu"] = (cur["hgf"] + cur["hga"]) / (2 * cur["hp"]) if cur["hp"] else (L["HA"] + L["AA"]) / 2
    for k in ("sotA", "bcA", "shA", "fk", "foul", "xg", "yellow"):
        c, p = cur.get(k), (pr_league or {}).get(k)
        L[k] = c if p is None else p if c is None else (c * cur["hp"] + p * K_LEAGUE) / (cur["hp"] + K_LEAGUE)
    L["sotA"] = L["sotA"] or 4.5
    L["bcA"] = L["bcA"] or 2.3
    L["yellowGame"] = 2 * (L["yellow"] or 2.1)
    L["shares"] = league_shares(matches, prior)   # quote reali dei titolari e tiri a partita, dalle partite ESPN
    # tiri e tiri in porta a partita di una squadra in questa stagione (ESPN, come quelli dei giocatori), con la
    # stagione scorsa come base nelle prime giornate
    for key, k in (("teamShots", "shots"), ("teamSot", "shotsOnTarget")):
        tot = sum(g(x["s"], k) or 0 for x in T.values())
        games = sum(g(x["s"], "matches") or 0 for x in T.values() if g(x["s"], k))
        base = (L["shares"] or {}).get(key)
        L[key] = (tot + (base or 0) * 60) / (games + 60) if games and base else (tot / games if games else base)

    # inizio di questa stagione: serve a capire se l'allenatore c'era già l'anno scorso
    pres = [e["start"] for e in (prior or {}).get("results") or [] if e.get("start")]
    cur_starts = [e["start"] for e in data.get("played") or [] if e.get("start")]
    season_start = max(pres) + 86400 if pres else (min(cur_starts) - 86400 if cur_starts else None)

    # forza delle squadre: stagione in corso + stagione scorsa come base
    for tid, t in T.items():
        t["pct"] = pct[tid]
        t["coach"] = coach_profile(tid, coaches, season_start)
        # panchina vacante: chi è andato via, quando e come (finché Wikipedia non indica il successore)
        t["vacant"] = None if t["coach"] else (((coaches or {}).get(tid) or {}).get("wiki") or {}).get("left")
        k_prior = K_PRIOR_NEW if t["coach"] and t["coach"]["same"] is False else K_PRIOR
        r = rating(t["m"], {"mu": L["mu"], "sotA": cur["sotA"] or L["sotA"], "bcA": cur["bcA"] or L["bcA"]})
        base = pr_rating.get(tid) or pr_rating.get("_promoted") or dict(NO_PRIOR, xg=L["mu"])
        t["prior"] = "stagione scorsa" if tid in pr_rating else "neopromossa (media delle ultime 5)" if "_promoted" in pr_rating else None
        w = t["n"] / (t["n"] + k_prior)
        t["att"] = w * r["att"] + (1 - w) * base["att"]
        t["de"] = w * r["de"] + (1 - w) * base["de"]
        t["xgBase"] = w * r["xg"] + (1 - w) * base.get("xg", r["xg"])
        t["priorWeight"] = 1 - w if t["prior"] else 0
        t["rank"], t["pct"], t["z"] = rank[tid], pct[tid], z[tid]
        t["style"] = style_tags(t["m"], t["pct"], t["rank"])
        t["dims"] = style_dims(t["pct"])
        t["arch"] = archetype(t["dims"])
        t["dimsPrev"] = prev_dims.get(tid)
        t["changes"] = style_changes(t["dims"], t["dimsPrev"])
        t["summary"] = style_summary(t)
        t["rel"] = reliance(tid, t["n"], players)
        count, last = formations_of(tid, matches)
        t["formations"], t["lastXI"] = count, last

    # medie per ruolo dei giocatori (per 90'), stagione in corso + scorsa
    pool = players + ((prior or {}).get("players") or [])
    posavg = {}
    for pos in ("G", "D", "M", "F"):
        grp = [p for p in pool if p.get("pos") == pos and (p.get("minutesPlayed") or 0) >= 270]
        mins = sum(p["minutesPlayed"] for p in grp)
        posavg[pos] = {}
        for k in PKEYS:
            have = [p for p in grp if num(p.get(k)) is not None]
            mm = sum(p["minutesPlayed"] for p in have)
            posavg[pos][k] = sum(p[k] for p in have) / mm * 90 if mm >= 900 else None
        posavg[pos]["_min"] = mins
    prior_players = {p["id"]: p for p in ((prior or {}).get("players") or [])}
    # ruoli valorizzati da ogni allenatore (partite di questa stagione e della scorsa, anche con altre squadre)
    league_roles = role_agg(role_rows or [])
    by_coach = {}
    for r in role_rows or []:
        k = coach_key(r.get("coach"))
        if k:
            by_coach.setdefault(k, []).append(r)
    for tid, t in T.items():
        c = (coaches or {}).get(tid) or {}
        name = (t.get("coach") or {}).get("name") or (c.get("wiki") or {}).get("name") or (c.get("manager") or {}).get("name")
        prof = role_profile(by_coach.get(coach_key(name), []), league_roles, (prior or {}).get("year")) if name else None
        t["coachRoles"] = dict(prof, coach=name, text=role_text(name, prof)) if prof else None
        rows_c = [r for r in by_coach.get(coach_key(name), []) if r.get("gf") is not None] if name else []
        if t.get("coach") and not (t["coach"].get("record") or {}).get("n") and rows_c:
            rec = {"n": 0, "w": 0, "d": 0, "l": 0, "gf": 0, "ga": 0, "over": 0, "cs": 0}
            for r in rows_c:
                gf, ga = r["gf"], r["ga"]
                rec["n"] += 1
                rec["w" if gf > ga else "d" if gf == ga else "l"] += 1
                rec["gf"] += gf
                rec["ga"] += ga
                rec["over"] += gf + ga > 2
                rec["cs"] += ga == 0
            t["coach"]["record"] = rec
            per_team = {}
            for x in (prof or {}).get("teams") or []:
                per_team[x["team"]] = per_team.get(x["team"], 0) + x["n"]
            t["coach"]["teams"] = sorted(per_team.items(), key=lambda kv: -kv[1])
    entries = []
    for e in (prior or {}).get("results") or []:
        ah, aa = prev_arch.get(str(e["home"]["id"])), prev_arch.get(str(e["away"]["id"]))
        if ah and aa and e.get("hs") is not None:
            entries.append((ah, aa, e["hs"], e["as"]))
    for e in data.get("played") or []:
        th, ta = T.get(str(e["home"]["id"])), T.get(str(e["away"]["id"]))
        if th and ta and e.get("hs") is not None:
            entries.append((th["arch"]["key"], ta["arch"]["key"], e["hs"], e["as"]))
    return {"T": T, "L": L, "players": {p["id"]: p for p in players}, "prior_players": prior_players,
            "posavg": posavg, "matches": matches, "hasPrior": bool(pr_rating), "priorYear": (prior or {}).get("year"),
            "archTable": arch_table(entries), "archMatches": len(entries)}


def public_analysis(A):
    teams = {}
    for tid, t in A["T"].items():
        rel = {k: v for k, v in t["rel"].items() if k != "shares"}
        fm = sorted(t["formations"].items(), key=lambda kv: -kv[1])
        teams[tid] = {"n": t["n"], "m": t["m"], "rank": t["rank"], "pct": t["pct"], "z": t["z"],
                      "form": t["ctx"]["form"][:10], "style": t["style"], "rel": rel,
                      "formations": [{"f": f, "n": c} for f, c in fm],
                      "rating": {"att": round(t["att"], 3), "de": round(t["de"], 3), "prior": t["prior"],
                                 "priorWeight": round(t["priorWeight"], 2)},
                      "dims": t["dims"], "dimsPrev": t["dimsPrev"], "arch": t["arch"], "changes": t["changes"],
                      "summary": t["summary"], "coach": t["coach"], "coachRoles": t.get("coachRoles"),
                      "vacant": t.get("vacant")}
    L = A["L"]
    return {"metrics": metrics_meta(), "teams": teams, "hasPrior": A["hasPrior"], "priorYear": A["priorYear"],
            "styleLabels": STYLE_LABELS, "archMatches": A.get("archMatches", 0),
            "league": {k: L[k] for k in ("HA", "AA", "N", "maxMin", "mu")}}


# ---------- pronostico ----------

PAIRS = [
    ("xg", "xga", "Occasioni create contro occasioni concesse"),
    ("sot", "gkp", "Tiri in porta contro il portiere"),
    ("corners", "air", "Palle inattive contro gioco aereo"),
    ("headed", "air", "Colpi di testa contro gioco aereo"),
    ("kp", "bcA", "Rifinitura contro difesa che lascia avvicinare"),
    ("bc", "shA", "Presenza vicino all'area contro tiri concessi"),
    ("cross", "crossA", "Cross contro difesa sulle fasce"),
    ("rec", "pass", "Aggressività contro costruzione imprecisa"),
]


def insights(X, Y, side, N):
    out = []
    for a, d, title in PAIRS:
        pa, pd = X["pct"].get(a), Y["pct"].get(d)
        if pa is None or pd is None:
            continue
        xs = f"{MK[a]['l']} {mval(a, X['m'][a])}{munit(a)}, {X['rank'][a]}ª su {N}"
        ys = f"{MK[d]['l']} {mval(d, Y['m'][d])}{munit(d)}, {Y['rank'][d]}ª su {N}"
        if pa >= .65 and pd <= .35:
            out.append({"side": side, "kind": "adv", "winner": X["id"], "eff": PAIR_ADV, "score": pa - pd, "title": title,
                        "lines": [[X["id"], MK[a]["S"], xs], [Y["id"], MK[d]["W"], ys]]})
        elif pa >= .7 and pd >= .7:
            out.append({"side": side, "kind": "duel", "winner": None, "eff": 0, "score": (pa + pd) / 2 - .5, "title": title,
                        "lines": [[X["id"], MK[a]["S"], xs], [Y["id"], MK[d]["S"], ys]]})
        elif pa <= .3 and pd >= .7:
            out.append({"side": side, "kind": "neut", "winner": Y["id"], "eff": PAIR_NEUT, "score": pd - pa - .1, "title": title,
                        "lines": [[Y["id"], MK[d]["S"], ys], [X["id"], MK[a]["W"], xs]]})
    return out


def pois(lam, n):
    p = [math.exp(-lam)]
    for i in range(1, n + 1):
        p.append(p[-1] * lam / i)
    return p


def score_matrix(lh, la):
    ph, pa = pois(lh, MAXG), pois(la, MAXG)
    mat, tot = [], 0.0
    for i in range(MAXG + 1):
        row = []
        for j in range(MAXG + 1):
            tau = 1.0
            if i == 0 and j == 0:
                tau = 1 - lh * la * RHO
            elif i == 0 and j == 1:
                tau = 1 + lh * RHO
            elif i == 1 and j == 0:
                tau = 1 + la * RHO
            elif i == 1 and j == 1:
                tau = 1 - RHO
            v = ph[i] * pa[j] * tau
            row.append(v)
            tot += v
        mat.append(row)
    return [[v / tot for v in row] for row in mat]


def outcome_probs(mat):
    res = {"p1": 0, "px": 0, "p2": 0, "over15": 0, "over25": 0, "over35": 0, "btts": 0, "csH": 0, "csA": 0}
    scores = []
    for i, row in enumerate(mat):
        for j, v in enumerate(row):
            if i > j:
                res["p1"] += v
            elif i == j:
                res["px"] += v
            else:
                res["p2"] += v
            if i + j > 1:
                res["over15"] += v
            if i + j > 2:
                res["over25"] += v
            if i + j > 3:
                res["over35"] += v
            if i and j:
                res["btts"] += v
            if j == 0:
                res["csH"] += v
            if i == 0:
                res["csA"] += v
            scores.append({"i": i, "j": j, "v": v})
    scores.sort(key=lambda s: -s["v"])
    return res, scores


# ---------- formazioni, duelli e proiezioni per giocatore ----------

PKEYS = ["totalShots", "shotsOnTarget", "fouls", "wasFouled", "yellowCards", "redCards", "expectedGoals", "expectedAssists",
         "goals", "assists", "saves", "keyPasses"]
YC_CONV_PRIOR = 60   # falli: quanto pesa la media del ruolo nel rapporto gialli/falli di un giocatore
# quanto conta l'avversario diretto sui falli: marcano soprattutto difensori e centrocampisti, gli attaccanti poco
DUEL_EXP = {"D": .6, "M": .45, "F": .2}


def card_conv(A, p):
    """Gialli per fallo del giocatore (questa stagione e la scorsa), avvicinati alla media del suo ruolo: in
    Serie A un attaccante prende un giallo ogni 10 falli circa, un difensore ogni 6. -> (gialli a fallo, del ruolo)"""
    pa = A["posavg"].get(p.get("pos") or "M") or {}
    base = pa["yellowCards"] / pa["fouls"] if pa.get("fouls") and pa.get("yellowCards") else 1 / 7
    pp = A["prior_players"].get(p.get("id")) or {}
    yc = (num(p.get("yellowCards")) or 0) + (num(pp.get("yellowCards")) or 0)
    fo = (num(p.get("fouls")) or 0) + (num(pp.get("fouls")) or 0)
    return clamp((yc + base * YC_CONV_PRIOR) / (fo + YC_CONV_PRIOR), .5 * base, 2 * base), base


def card_context(A, tid, oid):
    """Quanto dovrà difendere la squadra: chi ha meno palla fa più falli, e contro chi si procura tante
    punizioni se ne fanno di più. -> (fattore, possesso atteso, fattore del possesso, fattore delle punizioni)"""
    L, t, o = A["L"], A["T"][tid], A["T"][oid]
    pt, po = t["m"].get("poss"), o["m"].get("poss")
    poss = pt / (pt + po) if pt and po else .5
    poss_f = clamp(((1 - poss) / .5) ** .7, .75, 1.3)
    fk_f = clamp(((o["m"].get("fk") or L.get("fk") or 13) / (L.get("fk") or 13)) ** .4, .85, 1.2)
    return poss_f * fk_f, poss, poss_f, fk_f


def league_shares(matches, prior):
    """Quanto fanno davvero i titolari rispetto a tutta la squadra (minuti, tiri, tiri in porta, falli, falli subiti,
    gialli, gol, assist) e quanti tiri fa una squadra a partita, dalle partite ESPN di questa stagione e della scorsa
    (le stesse fonti delle statistiche dei giocatori). Cambia da lega a lega: in Serie A i cambi incidono di più che in
    Premier (titolari: 83% dei tiri e 81% dei gialli contro 86% e 86%)."""
    tot, n = {}, 0
    boxes = [x.get("box") for x in (matches or {}).values()]
    boxes += [v.get("box") for v in ((prior or {}).get("refCards") or {}).values()]
    for b in boxes:
        if not b or not b.get("players"):
            continue
        n += 1
        for side in ("home", "away"):
            for k in ("shots", "shotsOnTarget"):
                tot["team_" + k] = tot.get("team_" + k, 0) + ((b.get(side) or {}).get(k) or 0)
        for p in b["players"].values():
            who = "st" if p.get("start") else "sub"
            for k in ("min", "shots", "sot", "fouls", "fouled", "yc", "goals", "assists"):
                tot[f"{who}_{k}"] = tot.get(f"{who}_{k}", 0) + (p.get(k) or 0)
    if n < 30:
        return {}
    share = {k: tot.get(f"st_{k}", 0) / (tot.get(f"st_{k}", 0) + tot.get(f"sub_{k}", 0))
             for k in ("min", "shots", "sot", "fouls", "fouled", "yc", "goals", "assists") if tot.get(f"st_{k}")}
    return {"n": n, "share": share, "teamShots": tot.get("team_shots", 0) / (2 * n), "teamSot": tot.get("team_shotsOnTarget", 0) / (2 * n)}


def start_share(A, projs, key, default=.88):
    """Quota della statistica che fanno i titolari in questa partita: quella reale della lega, più alta o più bassa se
    i titolari previsti giocano più o meno minuti dei titolari di solito."""
    S = (A["L"].get("shares") or {}).get("share") or {}
    if key not in S or "min" not in S:
        return min(default, sum(p["min"] for p in projs) / 990)
    return clamp(S[key] * sum(p["min"] for p in projs) / (990 * S["min"]), .55, .97)


def anchor_team(A, projs, tid, oid, lam_team):
    """I numeri previsti dei titolari sommano a quelli realistici della squadra in questa partita, e i giocatori
    se li dividono secondo i loro numeri per 90' e i minuti previsti:
      - gol e assist: dai gol attesi della squadra (una parte la segnano i cambi, e ci sono gli autogol);
      - tiri e tiri in porta: quanti ne fa di solito, di più o di meno secondo quanto attaccherà in questa partita;
      - falli fatti: la sua media, con il possesso atteso e le punizioni che si procura l'avversario;
      - falli subiti: la sua media, con i falli che fa l'avversario.
    Le medie di squadra nelle prime giornate sono avvicinate a quelle della lega."""
    L, t, o = A["L"], A["T"][tid], A["T"][oid]
    # quota dei titolari: quella reale della lega per ogni statistica (prima era l'88% per tutto)
    sh = {k: start_share(A, projs, k) for k in ("shots", "sot", "fouls", "fouled", "goals", "assists")}
    # più o meno attacco del solito: gol attesi contro gli xG di base, centrato sul rapporto gol/xG della lega (senza,
    # valeva 0,93 in media e toglieva il 4% dei tiri a tutti)
    k_xg = L["mu"] / L["xg"] if L.get("xg") and L.get("mu") else 1.0
    rel = clamp(lam_team / ((t["xgBase"] or L["mu"]) * k_xg), .5, 2) ** .6
    n = t.get("n") or 0
    avg = lambda v, lg: (n * v + 5 * lg) / (n + 5) if v is not None and lg else lg
    s = t.get("s") or {}
    shots = s["shots"] / s["matches"] if s.get("shots") and s.get("matches") else None
    sot = s["shotsOnTarget"] / s["matches"] if s.get("shotsOnTarget") and s.get("matches") else t["m"].get("sot")
    SH = L.get("shares") or {}
    # medie di lega con le stesse fonti dei tiri dei giocatori (ESPN); i «tiri concessi» venivano da un'altra fonte
    # (di questa stagione: da un anno all'altro cambiano, in Serie A da 12,3 a 14,6 tiri a squadra)
    lg_shots = L.get("teamShots") or SH.get("teamShots") or L.get("shA")
    lg_sot = L.get("teamSot") or SH.get("teamSot") or L.get("sotA")
    goals = sum(num(p.get("goals")) or 0 for p in A["players"].values())
    ast_rate = sum(num(p.get("assists")) or 0 for p in A["players"].values()) / goals if goals else .7
    opp_fouls = avg(o["m"].get("foul"), L.get("foul")) if (o.get("n") or 0) else L.get("foul")
    # chance create: quante ne fa di solito la squadra (somma dei passaggi chiave dei suoi giocatori, Understat)
    kp_all = sum(num(p.get("keyPasses")) or 0 for p in A["players"].values())
    team_games = sum(x.get("n") or 0 for x in A["T"].values())
    kp_team = sum(num(p.get("keyPasses")) or 0 for p in A["players"].values() if str(p.get("teamId")) == str(tid))
    targets = {
        "lamG": lam_team * .97 * sh["goals"],
        "lamA": lam_team * ast_rate * sh["assists"],
        "shots": (avg(shots, lg_shots) or 0) * rel * sh["shots"],
        "sot": (avg(sot, lg_sot) or 0) * rel * sh["sot"],
        "kp": (avg(kp_team / n if n else None, kp_all / team_games if team_games else None) or 0) * rel * sh["shots"],
        "fouls": (avg(t["m"].get("foul"), L.get("foul")) or 0) * card_context(A, tid, oid)[0] * sh["fouls"],
        "fouled": (avg(t["m"].get("fk"), L.get("fk")) or 0)
                  * clamp(((opp_fouls or 1) / (L.get("foul") or opp_fouls or 1)) ** .6, .7, 1.4) * sh["fouled"],
    }
    # falli subiti: le punizioni a favore contano anche falli non attribuiti ai giocatori, si usa il rapporto reale
    pl_fouled = sum(num(p.get("wasFouled")) or 0 for p in A["players"].values())
    tm_fk = sum((x["m"].get("fk") or 0) * (x.get("n") or 0) for x in A["T"].values())
    if pl_fouled and tm_fk:
        targets["fouled"] *= clamp(pl_fouled / tm_fk, .6, 1)
    for k, target in targets.items():
        have = [p for p in projs if p.get(k)]
        rc = ROLE_CALIB.get("shots" if k == "sot" else k) or {}
        for p in have:   # taratura sulle partite reali, per ruolo
            p[k] *= rc.get(p.get("pos") or "M", 1.0) * (F_CALIB.get(k, 1) if p.get("pos") == "F" else 1)
        tot = sum(p[k] for p in have)
        if not tot or not target:
            continue
        for p in have:
            p[k] *= target / tot
    # nessuno si prende più del 40% dei gol previsti dei titolari (30% degli assist): nella realtà quasi nessuno ci arriva
    for k, cap in (("lamG", GOAL_SHARE_CAP), ("lamA", ASSIST_SHARE_CAP)):
        have = [p for p in projs if p.get(k)]
        tot = sum(p[k] for p in have)
        for _ in range(3):
            over = [p for p in have if p[k] > cap * tot + 1e-12]
            rest = [p for p in have if p not in over]
            rs = sum(p[k] for p in rest)
            if not over or not rs:
                break
            excess = sum(p[k] - cap * tot for p in over)
            for p in over:
                p[k] = cap * tot
            for p in rest:
                p[k] += excess * p[k] / rs
    for p in projs:
        if p.get("lamG") is not None:
            p["pGoal"] = 1 - math.exp(-p["lamG"])
        if p.get("lamA") is not None:
            p["pAssist"] = 1 - math.exp(-p["lamA"])


EVIDENZA = [("pGoal", "Marcatori", "%", "Probabilità di segnare almeno un gol"),
            ("pAssist", "Assist", "%", "Probabilità di fare almeno un assist"),
            ("shots", "Tiri", "n", "Tiri previsti nella partita"),
            ("sot", "Tiri in porta", "n", "Tiri in porta previsti nella partita"),
            ("kp", "Chance create", "n", "Passaggi che portano un compagno al tiro, previsti nella partita"),
            ("fouls", "Falli commessi", "n", "Falli che dovrebbe commettere"),
            ("fouled", "Falli subiti", "n", "Falli che dovrebbe subire"),
            ("pYellow", "Ammonizione", "%", "Probabilità di essere ammonito")]


# classifiche della stagione (dati reali): (campo, voce, cifre decimali, spiegazione, solo media)
EVIDENZA_STAGIONE = [
    ("goals", "Gol", 0, "Gol segnati", False),
    ("expectedGoals", "Expected goals (xG)", 1, "Gol attesi dalle occasioni avute: dice quanto è pericoloso, al di là dei gol fatti (Understat)", False),
    ("assists", "Assist", 0, "Assist", False),
    ("expectedAssists", "Expected assist (xA)", 1, "Assist attesi dai passaggi che hanno portato al tiro (Understat)", False),
    ("keyPasses", "Chance create", 0, "Passaggi che hanno portato un compagno al tiro (Understat)", False),
    ("totalShots", "Tiri", 0, "Tiri, dentro e fuori dallo specchio", False),
    ("shotsOnTarget", "Tiri in porta", 0, "Tiri nello specchio della porta (ESPN)", False),
    ("yellowCards", "Ammonizioni", 0, "Cartellini gialli", False),
    ("fouls", "Falli commessi", 0, "Falli fatti (ESPN)", False),
    ("wasFouled", "Falli subiti", 0, "Falli subiti (ESPN)", False),
    ("saves", "Parate", 0, "Parate dei portieri (ESPN)", False),
    ("fantamedia", "Fantamedia", 2, "Media fantavoto di Fantacalcio.it, con bonus e malus", True),
    ("rating", "Media voto", 2, "Media voto in pagella di Fantacalcio.it, senza bonus e malus", True),
]


def evidenza_stagione(A, n=10):
    """Classifiche della stagione con i dati reali: per ogni voce i primi 10 per totale e per media a partita.
    Nelle medie contano solo i giocatori con almeno il 60% delle presenze possibili (minimo 2), se no un giocatore
    con una presenza e un giallo sarebbe primo."""
    games = sorted(x.get("n") or 0 for x in A["T"].values())
    played = games[len(games) // 2] if games else 0
    min_apps = max(2, math.ceil(.6 * played))
    players = list(A["players"].values())
    cats = []
    for k, label, nd, desc, avg_only in EVIDENZA_STAGIONE:
        # le medie voto contano le partite con il voto, le altre le presenze
        apps_of = (lambda p: num(p.get("ratingPV")) or 0) if avg_only else (lambda p: num(p.get("appearances")) or 0)
        have = [p for p in players if num(p.get(k)) is not None and apps_of(p) > 0 and (avg_only or num(p[k]) > 0)]
        if not have:   # voce senza dati in questa lega (es. fantamedia fuori dalla Serie A)
            continue
        row = lambda p, v: {"id": p["id"], "name": (p.get("name") or "").strip(), "pos": p.get("pos"),
                            "team": str(p.get("teamId")), "v": round(v, 3), "tot": round(num(p[k]), 3),
                            "pg": round(num(p[k]) / apps_of(p), 3) if not avg_only else round(num(p[k]), 3),
                            "apps": int(apps_of(p)), "min": round(num(p.get("minutesPlayed")) or 0)}
        enough = [p for p in have if apps_of(p) >= min_apps]
        pg = sorted(enough, key=lambda p: (-(num(p[k]) / (1 if avg_only else apps_of(p))), -num(p[k]), p.get("name") or ""))[:n]
        c = {"k": k, "l": label, "d": desc, "nd": nd, "avg": avg_only,
             "pg": [row(p, num(p[k]) / (1 if avg_only else apps_of(p))) for p in pg]}
        if not avg_only:   # a parità di totale prima chi ha giocato meno
            tot = sorted(have, key=lambda p: (-num(p[k]), apps_of(p), num(p.get("minutesPlayed")) or 0, p.get("name") or ""))[:n]
            c["tot"] = [row(p, num(p[k])) for p in tot]
        cats.append(c)
    return {"games": played, "minApps": min_apps, "cats": cats}


def evidenza(items, n=10, A=None):
    """Giocatori in evidenza della giornata: per ogni statistica prevista, i primi 10 fra tutte le partite.
    items: [(partita, pronostico)]. Con A aggiunge le classifiche della stagione."""
    rows = [(p, e, side) for e, P in items for side in ("home", "away") for p in P["players"][side]]
    P_of = {e["id"]: P for e, P in items}
    cats = []
    for k, label, unit, desc in EVIDENZA:
        top = sorted((r for r in rows if r[0].get(k) is not None and r[0].get("pos") != "G"), key=lambda r: -r[0][k])[:n]
        cats.append({"k": k, "l": label, "u": unit, "d": desc, "rows": [
            {"id": p["id"], "name": (p.get("name") or "").strip(), "pos": p.get("pos"), "min": p.get("min"),
             "team": str(e[side]["id"]), "opp": str(e["away" if side == "home" else "home"]["id"]), "home": side == "home",
             "fid": e["id"], "start": e.get("start"), "v": round(p[k], 3),
             "official": P_of[e["id"]]["lineups"][side]["source"] == "ufficiale"} for p, e, side in top]})
    return {"round": items[0][0].get("round") if items else None, "cats": cats if items else [],
            "sources": sorted({P["lineups"][s]["source"] for _, P in items for s in ("home", "away")}),
            "season": evidenza_stagione(A, n) if A else None}


def anchor_cards(A, projs, tid, oid, card_f):
    """I gialli attesi dei titolari restano vicini a quanti ne prende di solito la squadra (con l'avversario,
    l'arbitro e l'intensità della partita): i singoli giocatori si dividono quel totale."""
    L, t = A["L"], A["T"][tid]
    have = [p for p in projs if p.get("lamY")]
    for p in have:   # quota reale dei gialli per ruolo nella lega
        p["lamY"] *= (ROLE_CALIB.get("lamY") or {}).get(p.get("pos") or "M", 1.0)
    tot = sum(p["lamY"] for p in have)
    cards = [x["m"]["card"] for x in A["T"].values() if x["m"].get("card") is not None]
    if not tot or not cards or t["m"].get("card") is None:
        return
    lg_card, n = sum(cards) / len(cards), t.get("n") or 0
    rel = (n * t["m"]["card"] + 6 * lg_card) / (n + 6) / lg_card   # cartellini della squadra rispetto alla media
    exp_team = (L.get("yellowGame") or 3.4) / 2 * rel * card_context(A, tid, oid)[0] * card_f
    share = start_share(A, projs, "yc")   # i gialli che prendono davvero i titolari nella lega (81-86%)
    # i titolari si dividono tutto il loro totale (prima solo in parte, con esponente 0,75: i gialli uscivano
    # sottostimati del 6% in Serie A e del 12% in Premier); arbitro e scontro di stili sono già in exp_team
    s = exp_team * share / tot
    for p in have:
        p["lamY"] *= s
        p["pYellow"] = 1 - math.exp(-p["lamY"])
    return exp_team * (1 - share)   # gialli attesi dei cambi


def parse_formation(f, n_outfield=10):
    try:
        lines = [int(x) for x in str(f).split("-")]
        if sum(lines) == n_outfield and all(x > 0 for x in lines):
            return lines
    except Exception:
        pass
    return None


def line_width(li, nl, k):
    """Metà larghezza occupata da un reparto (1 = fino alla linea laterale)."""
    if k == 1:
        return 0.0
    if k == 2:
        return .3
    if k == 3:
        return .8 if li == nl - 1 or (li == nl - 2 and nl >= 4) else .55
    return .85 if k == 4 else 1.0


def role_name(li, nl, k, j):
    x = 0.0 if k == 1 else line_width(li, nl, k) * (1 - 2 * j / (k - 1))
    outer = k >= 3 and j in (0, k - 1)
    side = " (destra)" if x > .2 else " (sinistra)" if x < -.2 else ""
    if li == 0:
        base = ("Terzino" if k == 4 else "Esterno") if k >= 4 and outer else "Difensore centrale"
    elif li == nl - 1:
        base = "Centravanti" if k == 1 else "Attaccante" if k == 2 else ("Ala" if outer else "Centravanti")
    elif li == nl - 2 and nl >= 4:
        base = "Esterno offensivo" if outer else "Trequartista"
    elif k <= 2:
        base = "Mediano"
    elif k == 3:
        base = "Mezzala" if outer else "Regista"
    else:
        base = "Esterno" if outer else "Centrocampista"
    return base, x, side


def xi_layout(xi):
    """Coordinate in campo di ogni titolare: x laterale (+1 destra, -1 sinistra), y profondità (0 porta, 1 attacco).

    Si assume che le formazioni elenchino i giocatori di ogni reparto da destra a sinistra.
    """
    starters = xi["starters"][:11]
    lines = parse_formation(xi.get("formation"))
    if not lines:
        counts = [sum(1 for p in starters[1:] if p.get("pos") == pos) for pos in ("D", "M", "F")]
        lines = [c for c in counts if c] or [4, 4, 2]
        if sum(lines) != len(starters) - 1:
            lines = [len(starters) - 1]
    out = {}
    if starters:
        out[starters[0]["id"]] = {"x": 0.0, "y": 0.0, "role": "Portiere", "side": ""}
    idx = 1
    for li, k in enumerate(lines):
        for j in range(k):
            if idx >= len(starters):
                break
            base, x, side = role_name(li, len(lines), k, j)
            if not xi.get("ordered", True):
                x, side = 0.0, ""   # formazione stimata: destra e sinistra non sono note
            out[starters[idx]["id"]] = {"x": x, "y": li / (len(lines) - 1) if len(lines) > 1 else .5,
                                        "role": base, "side": side}
            idx += 1
    return out


def direct_opponents(lay_h, lay_a):
    """Avversario diretto di ogni giocatore: il più vicino in campo, con le squadre una di fronte all'altra.

    I reparti occupano il campo dal 20% (difesa) al 75% (attacco) della propria metà verso la porta avversaria,
    così la difesa di una squadra si trova davanti all'attacco dell'altra.
    """
    res = {}
    at = lambda y: .2 + .55 * y
    for mine, theirs in ((lay_h, lay_a), (lay_a, lay_h)):
        for pid, c in mine.items():
            if c["role"] == "Portiere":
                continue
            best, bd = None, 9e9
            for oid, o in theirs.items():
                if o["role"] == "Portiere":
                    continue
                d = (c["x"] + o["x"]) ** 2 + 3 * (at(c["y"]) - (1 - at(o["y"]))) ** 2
                if d < bd:
                    best, bd = oid, d
            res[pid] = best
    return res


def estimate_xi(A, tid, missing_ids):
    """Formazione stimata: l'ultima schierata, sostituendo chi è indisponibile."""
    t = A["T"][tid]
    squad = sorted([p for p in A["players"].values() if str(p.get("teamId")) == tid],
                   key=lambda p: -(p.get("minutesPlayed") or 0))
    last = t.get("lastXI")
    if last:
        starters, used = [], set()
        for s in last["starters"][:11]:
            p = s
            if s["id"] in missing_ids or (s["id"] not in A["players"] and s.get("pos") != "G"):
                rep = next((q for q in squad if q.get("pos") == s.get("pos") and q["id"] not in missing_ids
                            and q["id"] not in used and all(q["id"] != x["id"] for x in last["starters"][:11])), None)
                p = {"id": rep["id"], "name": rep["name"], "pos": rep.get("pos")} if rep else s
            used.add(p["id"])
            starters.append({"id": p["id"], "name": p["name"], "pos": p.get("pos") or s.get("pos")})
        return {"formation": last.get("formation"), "starters": starters, "subs": [], "ordered": True}, "stimata dall'ultima partita"
    need, starters = {"G": 1, "D": 4, "M": 3, "F": 3}, []
    for pos in ("G", "D", "M", "F"):
        pick = [q for q in squad if q.get("pos") == pos and q["id"] not in missing_ids][:need[pos]]
        starters += [{"id": q["id"], "name": q["name"], "pos": pos} for q in pick]
    return {"formation": "4-3-3", "starters": starters, "subs": [], "ordered": False}, "stimata dal minutaggio"


def prate(A, p, key):
    """Statistica per 90' di un giocatore, avvicinata al dato di base (stagione scorsa o media di ruolo).
    Gol, assist, xG e xA sono rari e casuali: servono più minuti prima di fidarsi del dato del giocatore, e
    anche la stagione scorsa, se breve, viene avvicinata alla media del ruolo."""
    pos = p.get("pos") or "M"
    pos_base = (A["posavg"].get(pos) or {}).get(key)
    rare = key in RARE_KEYS
    base = pos_base
    pp = A["prior_players"].get(p.get("id"))
    if pp and (pp.get("minutesPlayed") or 0) >= 450 and num(pp.get(key)) is not None:
        pm = pp["minutesPlayed"]
        base = (pp[key] + pos_base * RARE_PRIOR_MIN / 90) / ((pm + RARE_PRIOR_MIN) / 90) if rare and pos_base is not None \
            else pp[key] / pm * 90
    cnt, m = num(p.get(key)), num(p.get("minutesPlayed")) or 0
    if cnt is None:
        cnt, m = 0.0, 0.0
        if base is None:
            return None
    if base is None:
        base = cnt / m * 90 if m else 0.0
    k = RARE_PRIOR_MIN if rare else PLAYER_PRIOR_MIN
    return (cnt + base * k / 90) / ((m + k) / 90)


STARTER_MIN = {"G": 90, "D": 84, "M": 77, "F": 74}   # minuti medi reali dei titolari in Serie A, per ruolo


def exp_minutes(p, starter):
    """Minuti attesi: metà dal giocatore, metà dalla media reale dei titolari del suo ruolo (centrocampisti e
    attaccanti vengono sostituiti spesso)."""
    if not starter:
        return 12.0
    pos_min = STARTER_MIN.get(p.get("pos") or "M", 78)
    apps, started, mins = p.get("appearances") or 0, p.get("matchesStarted"), p.get("minutesPlayed") or 0
    if started:
        avg = (mins - 20 * max(0, apps - started)) / started
    elif apps:
        avg = mins / apps * 1.15
    else:
        return float(pos_min)
    return clamp(.5 * clamp(avg, 55, 90) + .5 * pos_min, 55, 90)


def player_projections(A, tid, oid, xi, lay, opp_lay, opp_xi, duels, lam_team, lam_opp, ref_factor):
    T, L = A["T"], A["L"]
    t, o = T[tid], T[oid]
    ratio_ = clamp(lam_team / (t["xgBase"] or L["mu"]), .4, 2.5)
    shot_f = clamp((o["m"].get("shA") or L["shA"] or 12) / (L["shA"] or 12), .6, 1.6)
    foul_f = clamp((o["m"].get("foul") or L["foul"] or 13) / (L["foul"] or 13), .7, 1.4) if L.get("foul") else 1.0
    team_card, poss, poss_f, fk_f = card_context(A, tid, oid)
    opp_by_id = {p["id"]: p for p in opp_xi["starters"]}
    out = []
    for s in xi["starters"][:11]:
        p = dict(A["players"].get(s["id"]) or {"id": s["id"], "name": s["name"]})
        p.setdefault("pos", s.get("pos"))
        c = lay.get(s["id"], {"role": "", "side": ""})
        mins = exp_minutes(p, True)
        f = mins / 90
        r = {k: prate(A, p, k) for k in PKEYS}
        opp_id = duels.get(s["id"])
        opp = A["players"].get(opp_id) or ({"id": opp_id, "name": opp_by_id[opp_id]["name"]} if opp_id in opp_by_id else None)
        # chi marca chi: contro un avversario diretto che subisce tanti falli se ne fanno di più
        duel_f, opp_wf = 1.0, None
        if opp:
            oposp = dict(opp)
            oposp.setdefault("pos", (opp_by_id.get(opp_id) or {}).get("pos"))
            opp_wf = prate(A, oposp, "wasFouled")
            base = (A["posavg"].get(oposp.get("pos") or "M") or {}).get("wasFouled")
            if base and opp_wf is not None:
                duel_f = clamp((opp_wf / base) ** DUEL_EXP.get(p.get("pos") or "M", .45), .75, 1.6)
        # giallo: falli che farà (suoi, dell'avversario diretto e di quanto difenderà la squadra) per i gialli
        # che prende a fallo, con arbitro e intensità della partita; il totale di squadra lo fissa anchor_cards.
        # I portieri no: prendono gialli per perdita di tempo, non per falli
        conv, conv_pos = card_conv(A, p)
        exp_fouls = r["fouls"] * f * duel_f * team_card if r["fouls"] is not None else None
        if p.get("pos") == "G":
            lam_y = r["yellowCards"] * f * ref_factor if r["yellowCards"] is not None else None
        else:
            lam_y = exp_fouls * conv * ref_factor if exp_fouls is not None else None
        xg90 = r["expectedGoals"] if r["expectedGoals"] is not None else r["goals"]
        xa90 = r["expectedAssists"] if r["expectedAssists"] is not None else r["assists"]
        g90 = .8 * (xg90 or 0) + .2 * (r["goals"] or 0)
        a90 = .8 * (xa90 or 0) + .2 * (r["assists"] or 0)
        proj = {
            "id": s["id"], "name": p.get("name") or s.get("name"), "pos": p.get("pos"), "role": c["role"] + c["side"],
            "min": round(mins), "rating": p.get("rating"),
            "shots": r["totalShots"] * f * shot_f ** .7 * ratio_ ** .5 if r["totalShots"] is not None else None,
            "sot": r["shotsOnTarget"] * f * shot_f ** .7 * ratio_ ** .5 if r["shotsOnTarget"] is not None else None,
            "kp": r["keyPasses"] * f * shot_f ** .7 * ratio_ ** .5 if r["keyPasses"] is not None else None,
            "fouls": exp_fouls,
            "fouled": r["wasFouled"] * f * foul_f if r["wasFouled"] is not None else None,
            "pYellow": 1 - math.exp(-lam_y) if lam_y is not None else None,
            "pRed": 1 - math.exp(-r["redCards"] * f * ref_factor) if r["redCards"] is not None else None,
            "pGoal": 1 - math.exp(-g90 * f * ratio_) if p.get("pos") != "G" else 0.0,
            "pAssist": 1 - math.exp(-a90 * f * ratio_) if p.get("pos") != "G" else 0.0,
            "lamG": g90 * f * ratio_ if p.get("pos") != "G" else 0.0,
            "lamA": a90 * f * ratio_ if p.get("pos") != "G" else 0.0,
            "saves": r["saves"] * f * clamp(lam_opp / L["mu"], .5, 2) if p.get("pos") == "G" and r["saves"] is not None else None,
            "opp": {"id": opp_id, "name": opp.get("name"), "role": (opp_lay.get(opp_id) or {}).get("role", "")
                    + (opp_lay.get(opp_id) or {}).get("side", "")} if opp else None,
            "lamY": lam_y,
            # da cosa dipende il rischio di giallo (serve a spiegarlo nella pagina)
            "yWhy": {"fouls": r["fouls"], "foulsPos": (A["posavg"].get(p.get("pos") or "M") or {}).get("fouls"),
                     "duel": duel_f, "oppWf": opp_wf, "poss": poss, "possF": poss_f, "fk": fk_f,
                     "conv": conv, "convPos": conv_pos, "yc": p.get("yellowCards"), "apps": p.get("appearances")},
        }
        out.append(proj)
    coach_role_shift(t, out, lay)
    return out


def coach_role_shift(t, out, lay):
    """Sposta una parte dei gol e degli assist attesi verso i ruoli che l'allenatore valorizza (e via da quelli che
    valorizza meno), senza cambiare il totale della squadra. Effetto massimo circa ±25% per giocatore."""
    prof = t.get("coachRoles") or {}
    idx = {r["f"]: r for r in prof.get("roles") or []} if prof.get("n", 0) >= 3 else {}
    if not idx:
        return
    power = .5 * min(1.0, prof["n"] / 15)   # con poche partite dell'allenatore l'effetto si riduce
    for lam, ik, pk in (("lamG", "gIdx", "pGoal"), ("lamA", "aIdx", "pAssist")):
        items = [o for o in out if o.get(lam)]
        w = {o["id"]: clamp((idx.get(ROLE_FAMILY.get((lay.get(o["id"]) or {}).get("role"))) or {}).get(ik, 1.0), .6, 1.6) ** power
             for o in items}
        tot, new = sum(o[lam] for o in items), sum(o[lam] * w[o["id"]] for o in items)
        if not tot or not new:
            continue
        for o in items:
            o[lam] *= w[o["id"]] * tot / new
            o[pk] = 1 - math.exp(-o[lam])
            o["coachF" + ik[0]] = round(w[o["id"]] * tot / new, 2)


def side_out_cautioned(xi):
    return {norm_name(n) for n in xi.get("cautioned") or []}


def norm_name(n):
    return " ".join(norm_tokens(n))


def yellow_risk(proj_h, proj_a, hid, aid, cautioned, ref, ref_f, ref_ypg, clash_cards):
    """I giocatori più a rischio di ammonizione nella partita, con il perché (falli che fa, chi marca, quanto
    difenderà la squadra, quanti falli gli servono per un giallo), più i diffidati: con un giallo saltano la
    partita dopo."""
    rows, diffidati = [], []
    for key, tid, projs in (("h", hid, proj_h), ("a", aid, proj_a)):
        for p in projs:
            if p.get("pYellow") is None:
                continue
            w = p.get("yWhy") or {}
            why = []
            fo, fp = w.get("fouls"), w.get("foulsPos")
            if fo is not None and fp and fo >= 1.2 * fp:
                why.append(f"fa tanti falli: {fmt(fo, 1)} a partita (media del ruolo {fmt(fp, 1)})")
            if (w.get("duel") or 1) >= 1.1 and p.get("opp") and w.get("oppWf") is not None:
                why.append(f"{'si trova davanti' if p.get('pos') == 'F' else 'marca'} {p['opp']['name']}, "
                           f"che subisce {fmt(w['oppWf'], 1)} falli a partita")
            if (w.get("possF") or 1) >= 1.08:
                why.append(f"la sua squadra avrà meno palla (possesso atteso {fmt((w.get('poss') or .5) * 100, 0)}%)")
            conv, cp = w.get("conv"), w.get("convPos")
            if conv and cp and conv >= 1.3 * cp:
                why.append(f"si fa ammonire spesso: un giallo ogni {fmt(1 / conv, 0)} falli (nel suo ruolo uno ogni {fmt(1 / cp, 0)})")
            if (w.get("fk") or 1) >= 1.08:
                why.append("contro una squadra che si procura tante punizioni")
            yc, apps = int(w.get("yc") or 0), int(w.get("apps") or 0)
            if yc and apps and len(why) < 3:
                why.append(f"{yc} {'giallo' if yc == 1 else 'gialli'} in {apps} {'presenza' if apps == 1 else 'presenze'} quest'anno")
            if not why:
                why.append("rischio nella media del suo ruolo")
            dif = norm_name(p.get("name")) in cautioned[key]
            row = {"id": p["id"], "name": p["name"], "team": int(tid), "role": p.get("role"), "p": p["pYellow"],
                   "why": why[:3], "diffidato": dif}
            rows.append(row)
            if dif:
                diffidati.append(row)
    rows.sort(key=lambda r: -r["p"])
    ctx = []
    if ref and ref.get("games"):
        ctx.append(f"Arbitro {ref['name']}: {fmt(ref_ypg, 1)} gialli a partita "
                   f"({'+' if ref_f >= 1 else ''}{fmt((ref_f - 1) * 100, 0)}% sui cartellini attesi)")
    elif ref:
        ctx.append(f"Arbitro {ref['name']}: nessuna sua partita nei dati, effetto neutro")
    if clash_cards >= .05:
        ctx.append(f"partita intensa per lo scontro di stili (+{fmt(clash_cards * 100, 0)}% sui cartellini)")
    return {"top": rows[:6], "diffidati": sorted(diffidati, key=lambda r: -r["p"]),
            "context": ". ".join(c[0].upper() + c[1:] for c in ctx) + ("." if ctx else "")}


def missing_label(m):
    desc = (m.get("desc") or "").lower()
    if m.get("type") == "doubtful":
        return "In dubbio"
    if any(w in desc for w in ("susp", "card", "squalif", "ban", "red")):
        return "Squalificato"
    if m.get("reason") in (3, 5) and not desc:
        return "Squalificato"
    return "Infortunato" if desc or m.get("reason") in (1, 2) else "Indisponibile"


def absences(A, tid, side, confirmed):
    """Giocatori importanti che non giocano e il loro effetto su attacco e difesa."""
    t = A["T"][tid]
    sh = t["rel"].get("shares", {})
    regulars = [pid for pid, x in sh.items() if x["min"] >= .4]
    missing = {m["id"]: m for m in (side or {}).get("missing") or [] if m.get("id")}
    starters = {p["id"] for p in (side or {}).get("starters") or []}
    out = []
    for pid in regulars:
        if len(starters) >= 11 and pid not in starters:
            w = 1.0 if confirmed else .7
            why = missing_label(missing[pid]) if pid in missing else "Non titolare" if confirmed else "Non nella formazione probabile"
        elif pid in missing:
            w = .5 if missing[pid].get("type") == "doubtful" else 1.0
            why = missing_label(missing[pid])
        else:
            continue
        p = A["players"].get(pid) or {}
        out.append({"id": pid, "name": p.get("name"), "pos": sh[pid]["pos"], "w": w, "why": why,
                    "att": sh[pid]["att"], "def": sh[pid]["def"], "min": sh[pid]["min"]})
    att = min(.3, sum(x["w"] * x["att"] * .45 for x in out))
    de = min(.2, sum(x["w"] * x["def"] * .35 for x in out) + sum(.06 * x["w"] for x in out if x["pos"] == "G"))
    return out, att, de


def referee_factor(A, ref):
    if not ref or not ref.get("games"):
        return 1.0, None
    ypg = ((ref.get("yellow") or 0) + (ref.get("yellowRed") or 0)) / ref["games"]
    base = ref.get("base") or A["L"]["yellowGame"]   # media delle stesse partite da cui viene il suo dato
    rel = ypg / base if base else 1
    w = ref["games"] / (ref["games"] + 10)
    return clamp(w * rel + (1 - w), .75, 1.3), ypg


def predict(A, hid, aid, ev=None, extra=None):
    hid, aid = str(hid), str(aid)
    T, L = A["T"], A["L"]
    H, Aw = T[hid], T[aid]
    adj = []

    def shr(r, n, k):
        return (n * r + k) / (n + k)

    attH, deH, attA, deA = (x ** CALIB for x in (H["att"], H["de"], Aw["att"], Aw["de"]))
    hr, ar = H["ctx"]["home"], Aw["ctx"]["away"]
    if hr and hr.get("p"):
        attH = .8 * attH + .2 * shr(hr["gf"] / hr["p"] / L["HA"], hr["p"], 4)
        deH = .8 * deH + .2 * shr(hr["ga"] / hr["p"] / L["AA"], hr["p"], 4)
    if ar and ar.get("p"):
        attA = .8 * attA + .2 * shr(ar["gf"] / ar["p"] / L["AA"], ar["p"], 4)
        deA = .8 * deA + .2 * shr(ar["ga"] / ar["p"] / L["HA"], ar["p"], 4)
    lh, la = L["HA"] * attH * deA, L["AA"] * attA * deH
    base_h, base_a = lh, la

    fh, fa = H["m"].get("form"), Aw["m"].get("form")
    fd = ((fh if fh is not None else 1.4) - (fa if fa is not None else 1.4)) / 3
    if abs(fd) > .05:
        adj.append({"team": int(hid), "what": "Forma recente", "pct": FORM_EFF * 100 * fd})
        adj.append({"team": int(aid), "what": "Forma recente", "pct": -FORM_EFF * 100 * fd})
    lh *= 1 + FORM_EFF * fd
    la *= 1 - FORM_EFF * fd

    ins = sorted(insights(H, Aw, "h", L["N"]) + insights(Aw, H, "a", L["N"]), key=lambda i: -i["score"])
    bh = clamp(sum(i["eff"] for i in ins if i["side"] == "h"), -PAIR_CAP, PAIR_CAP)
    ba = clamp(sum(i["eff"] for i in ins if i["side"] == "a"), -PAIR_CAP, PAIR_CAP)
    if bh:
        adj.append({"team": int(hid), "what": "Accoppiamenti tattici", "pct": bh * 100})
    if ba:
        adj.append({"team": int(aid), "what": "Accoppiamenti tattici", "pct": ba * 100})
    lh *= 1 + bh
    la *= 1 + ba

    # scontro di stili
    clash = style_clash(H, Aw, A)
    for key, tid in (("h", hid), ("a", aid)):
        if clash["eff"][key]:
            adj.append({"team": int(tid), "what": "Scontro di stili", "pct": clash["eff"][key] * 100})
        if clash["tempo"]:
            adj.append({"team": int(tid), "what": "Ritmo della partita (scontro di stili)", "pct": clash["tempo"] * 100})
    lh *= (1 + clash["eff"]["h"]) * (1 + clash["tempo"])
    la *= (1 + clash["eff"]["a"]) * (1 + clash["tempo"])
    # forma, accoppiamenti, stili e ritmo tendono a premiare la squadra più forte: insieme non spostano i gol
    # attesi più di SOFT_CAP (come nelle quote reali, dove questi fattori contano poco)
    for tid, lam, base in ((hid, lh, base_h), (aid, la, base_a)):
        capped = clamp(lam, base * (1 - SOFT_CAP), base * (1 + SOFT_CAP))
        if abs(capped - lam) > 1e-9:
            adj.append({"team": int(tid), "what": f"Tetto alle correzioni qui sopra (insieme al massimo ±{SOFT_CAP * 100:.0f}%)",
                        "pct": (capped / lam - 1) * 100})
        if tid == hid:
            lh = capped
        else:
            la = capped

    # formazioni e assenti
    lu = (extra or {}).get("lineups")
    confirmed = bool(lu and lu.get("confirmed"))
    sides = {"h": (lu or {}).get("home"), "a": (lu or {}).get("away")}
    absent = {}
    for key, tid, oppkey in (("h", hid, "a"), ("a", aid, "h")):
        lst, att_loss, def_loss = absences(A, tid, sides[key], confirmed)
        absent[key] = lst
        opp_id = aid if key == "h" else hid
        if att_loss:
            names = ", ".join(x["name"] or "?" for x in lst if x["att"] >= .05)
            adj.append({"team": int(tid), "what": f"Assenti in attacco: {names}" if names else "Assenti in attacco", "pct": -att_loss * 100})
        if def_loss:
            names = ", ".join(x["name"] or "?" for x in lst if x["def"] >= .05 or x["pos"] == "G")
            who = T[tid]["team"]["name"]
            adj.append({"team": int(opp_id), "what": f"Assenti in difesa di {who}: {names}" if names else f"Assenti in difesa di {who}",
                        "pct": def_loss * 100})
        if key == "h":
            lh *= 1 - att_loss
            la *= 1 + def_loss
        else:
            la *= 1 - att_loss
            lh *= 1 + def_loss
    lh, la = clamp(lh, .2, 4.5), clamp(la, .2, 4.5)

    mat = score_matrix(lh, la)
    res, scores = outcome_probs(mat)
    outs = [("1", res["p1"], lambda s: s["i"] > s["j"], "Vittoria " + H["team"]["name"]),
            ("X", res["px"], lambda s: s["i"] == s["j"], "Pareggio"),
            ("2", res["p2"], lambda s: s["i"] < s["j"], "Vittoria " + Aw["team"]["name"])]
    best = max(outs, key=lambda o: o[1])
    pick_score = next(s for s in scores if best[2](s))
    pick = {"k": best[0], "p": best[1], "label": best[3], "score": {"i": pick_score["i"], "j": pick_score["j"]}}

    # formazioni: ufficiali (ESPN), probabili (Fantacalcio.it) o stimate
    xis, src = {}, {}
    for key, tid in (("h", hid), ("a", aid)):
        side = sides[key]
        miss = {m["id"] for m in (side or {}).get("missing") or [] if m.get("id") and m.get("type") != "doubtful"}
        if side and len(side.get("starters") or []) >= 11:
            xis[key], src[key] = side, "ufficiale" if confirmed else (
                {"fantacalcio": "probabile (Fantacalcio.it)", "onefootball": "probabile (OneFootball)"}.get((lu or {}).get("source"), "probabile"))
        else:
            xis[key], src[key] = estimate_xi(A, tid, miss)
    ref = (extra or {}).get("referee")
    ref_f, ref_ypg = referee_factor(A, ref)
    lay_h, lay_a = xi_layout(xis["h"]), xi_layout(xis["a"])
    ordered = xis["h"].get("ordered", True) and xis["a"].get("ordered", True)
    duels = direct_opponents(lay_h, lay_a) if ordered else {}
    card_f = ref_f * (1 + clash["cards"])   # arbitro e scontro di stili
    proj_h = player_projections(A, hid, aid, xis["h"], lay_h, lay_a, xis["a"], duels, lh, la, card_f)
    proj_a = player_projections(A, aid, hid, xis["a"], lay_a, lay_h, xis["h"], duels, la, lh, card_f)
    subs_h = anchor_cards(A, proj_h, hid, aid, card_f)
    subs_a = anchor_cards(A, proj_a, aid, hid, card_f)
    anchor_team(A, proj_h, hid, aid, lh)
    anchor_team(A, proj_a, aid, hid, la)
    cards_h = sum(p["lamY"] or 0 for p in proj_h) + (subs_h if subs_h is not None else .15)
    cards_a = sum(p["lamY"] or 0 for p in proj_a) + (subs_a if subs_a is not None else .15)
    for p in proj_h + proj_a:
        p.pop("lamY", None)
    lu_out = {"h": side_out_cautioned(xis["h"]), "a": side_out_cautioned(xis["a"])}
    yellow = yellow_risk(proj_h, proj_a, hid, aid, lu_out, ref, ref_f, ref_ypg, clash["cards"])

    def side_out(key, tid):
        s = xis[key]
        miss = [{"id": m.get("id"), "name": m.get("name"), "pos": m.get("pos"), "why": missing_label(m), "desc": m.get("desc")}
                for m in (sides[key] or {}).get("missing") or []]
        pct = {p["id"]: p["pct"] for p in (s.get("starters") or []) + (s.get("subs") or []) if p.get("pct") is not None}
        return {"formation": s.get("formation"), "source": src[key], "missing": miss, "pct": pct,
                "cautioned": s.get("cautioned") or [],
                "subs": [{"id": p["id"], "name": p["name"], "pos": p.get("pos")} for p in s.get("subs") or []]}

    return {
        "home": int(hid), "away": int(aid), "eventId": (ev or {}).get("id"), "start": (ev or {}).get("start"),
        "round": (ev or {}).get("round"), "lh": lh, "la": la, "baseH": base_h, "baseA": base_a, **res,
        "scores": scores[:8], "mat": [row[:6] for row in mat[:6]], "pick": pick,
        "top": {"i": scores[0]["i"], "j": scores[0]["j"], "p": scores[0]["v"]},
        "ins": ins[:8], "adj": adj, "absent": {"home": absent["h"], "away": absent["a"]},
        "lineups": {"confirmed": confirmed, "home": side_out("h", hid), "away": side_out("a", aid)},
        "players": {"home": proj_h, "away": proj_a},
        "cards": {"home": cards_h, "away": cards_a},
        "yellowRisk": yellow,
        "referee": dict(ref, ypg=ref_ypg, factor=ref_f) if ref else None,
        "style": {"home": {"arch": H["arch"], "dims": H["dims"], "coach": H["coach"]},
                  "away": {"arch": Aw["arch"], "dims": Aw["dims"], "coach": Aw["coach"]},
                  "items": clash["items"], "tempo": clash["tempo"], "cards": clash["cards"], "poss": clash["poss"],
                  "matches": A.get("archMatches", 0)},
        "h2h": (extra or {}).get("h2h"),
        "coachRoles": {"home": (H.get("coachRoles") or {}).get("text"), "away": (Aw.get("coachRoles") or {}).get("text")},
        "prior": {"home": H["prior"], "away": Aw["prior"], "weightH": H["priorWeight"], "weightA": Aw["priorWeight"],
                  "year": A["priorYear"]},
    }


def summary(P):
    return {k: P[k] for k in ("p1", "px", "p2", "lh", "la", "over25", "btts", "pick", "top")} | {
        "lineups": "ufficiale" if P["lineups"]["confirmed"] else P["lineups"]["home"]["source"]}


# ---------- storico dei pronostici ----------

def update_history(H, A, data, matches, now=None, ids=None):
    """Salva l'ultimo pronostico prima del calcio d'inizio e lo confronta con il risultato. ids: id ESPN dei giocatori
    -> id dell'anagrafica (quelli delle formazioni), per agganciare le statistiche vere alle previsioni."""
    now = now or time.time()
    items = H.setdefault("matches", {})
    changed = False
    for e in data.get("next") or []:
        if e.get("status") != "notstarted" or not (0 < e["start"] - now <= 7 * 86400):
            continue
        if str(e["home"]["id"]) not in A["T"] or str(e["away"]["id"]) not in A["T"]:
            continue
        P = predict(A, e["home"]["id"], e["away"]["id"], e, matches.get(str(e["id"])))
        it = items.setdefault(str(e["id"]), {"id": e["id"], "round": e.get("round"), "start": e["start"],
                                            "home": e["home"], "away": e["away"]})
        it["start"] = e["start"]
        it["latest"] = dict(summary(P), at=now, pl=history_players(P), cards=[round(P["cards"]["home"], 2),
                            round(P["cards"]["away"], 2)], ref=(P.get("referee") or {}).get("name"))
        changed = True
    for eid, it in items.items():
        if "final" not in it and it.get("latest") and now >= it["start"]:
            it["final"] = it["latest"]
            changed = True
    for e in data.get("played") or []:
        it = items.get(str(e["id"]))
        if it and it.get("final") and "result" not in it and e.get("hs") is not None:
            it["result"] = {"hs": e["hs"], "as": e["as"]}
            it["eval"] = evaluate(it["final"], e["hs"], e["as"])
            changed = True
    # le statistiche vere dei giocatori (ESPN) arrivano poco dopo il risultato
    for eid, it in items.items():
        box = (matches.get(eid) or {}).get("box")
        if it.get("result") and "real" not in it and box and box.get("players"):
            it["real"] = history_real(box, ids)
            changed = True
    return changed


def history_players(P):
    """Le previsioni dei titolari da salvare nello storico, per confrontarle poi con la partita vera:
    [id, nome, minuti, tiri, tiri in porta, falli, prob. di giallo, prob. di gol, chance create]."""
    r = lambda v, n=2: round(v, n) if v is not None else None
    return {side: [[p["id"], p.get("name"), p.get("min"), r(p.get("shots")), r(p.get("sot")), r(p.get("fouls")),
                    r(p.get("pYellow"), 3), r(p.get("pGoal"), 3), r(p.get("kp"))] for p in P["players"][side]]
            for side in ("home", "away")}


def history_real(box, ids=None):
    """Le statistiche vere della partita (ESPN): per giocatore [squadra, minuti, tiri, tiri in porta, falli, gialli,
    gol, assist, titolare], più i totali delle squadre."""
    g = lambda p, k: p.get(k) or 0
    return {"players": {str((ids or {}).get(str(pid), pid)): [p.get("side"), g(p, "min"), g(p, "shots"), g(p, "sot"), g(p, "fouls"), g(p, "yc"),
                                   g(p, "goals"), g(p, "assists"), bool(p.get("start"))] for pid, p in box["players"].items()},
            "team": {s: {k: (box.get(s) or {}).get(k) for k in ("shots", "shotsOnTarget", "fouls", "yellowCards")}
                     for s in ("home", "away")}}


def evaluate(f, hs, as_):
    o = "1" if hs > as_ else "X" if hs == as_ else "2"
    probs = {"1": f["p1"], "X": f["px"], "2": f["p2"]}
    return {
        "outcome": o,
        "pick": f["pick"]["k"] == o,
        "score": f["pick"]["score"]["i"] == hs and f["pick"]["score"]["j"] == as_,
        "topScore": f["top"]["i"] == hs and f["top"]["j"] == as_,
        "over25": (f["over25"] > .5) == (hs + as_ > 2),
        "btts": (f["btts"] > .5) == (hs > 0 and as_ > 0),
        "brier": sum((probs[k] - (1 if k == o else 0)) ** 2 for k in probs),
    }


def history_summary(H):
    done = [it for it in H.get("matches", {}).values() if it.get("eval")]
    n = len(done)
    if not n:
        return {"n": 0}
    s = lambda k: sum(1 for it in done if it["eval"][k]) / n
    base = {"1": .44, "X": .27, "2": .29}  # frequenze storiche della Serie A
    base_brier = sum(sum((base[k] - (1 if k == it["eval"]["outcome"] else 0)) ** 2 for k in base) for it in done) / n
    # affidabilità: quando il pronostico dava il suo esito al 50-60%, quante volte ci ha preso davvero
    cal = []
    for lo, hi in ((0, .45), (.45, .55), (.55, .65), (.65, 1.01)):
        g = [it for it in done if lo <= (it["final"]["pick"].get("p") or 0) < hi]
        if g:
            cal.append({"lo": lo, "hi": min(hi, 1), "n": len(g), "p": sum(it["final"]["pick"]["p"] for it in g) / len(g),
                        "hit": sum(1 for it in g if it["eval"]["pick"]) / len(g)})
    # giocatori: totali previsti per i titolari contro quelli veri (gialli, tiri, falli, gol)
    pl = {"n": 0, "y": [0.0, 0], "shots": [0.0, 0], "fouls": [0.0, 0], "goals": [0.0, 0]}
    for it in done:
        real = (it.get("real") or {}).get("players") or {}
        rows = [p for side in ("home", "away") for p in ((it["final"].get("pl") or {}).get(side) or [])]
        if not real or not rows:
            continue
        pl["n"] += 1
        for p in rows:
            r = real.get(str(p[0]))
            if not r:
                continue
            for k, pi, ri in (("y", 6, 5), ("shots", 3, 2), ("fouls", 5, 4), ("goals", 7, 6)):
                pl[k][0] += p[pi] or 0
                pl[k][1] += min(r[ri], 1) if k in ("y", "goals") else r[ri]
    return {"n": n, "pick": s("pick"), "score": s("score"), "over25": s("over25"), "btts": s("btts"),
            "brier": sum(it["eval"]["brier"] for it in done) / n, "baseBrier": base_brier, "cal": cal,
            "players": pl if pl["n"] else None}


# ---------- fantacalcio ----------

FANTA_RULES = {
    "voto": 6.0, "gol": 3.0, "assist": 1.0, "ammonizione": -0.5, "espulsione": -1.0,
    "golSubito": -1.0, "portaInviolata": 1.0, "modDifesa": True, "switch": False,
}
# modificatore di difesa: media voto (senza bonus/malus) del portiere e dei 3 migliori difensori,
# solo schierando almeno 4 difensori. Soglie e bonus: [media minima, bonus]
MOD_TABLE = [[6.0, 1.0], [6.25, 1.5], [6.5, 2.0], [6.75, 2.5], [7.0, 3.0]]


def mod_bands(table):
    t = sorted(table)
    return [(lo, t[i + 1][0] if i + 1 < len(t) else 99.0, b) for i, (lo, b) in enumerate(t)]
MOD_SD = .45   # incertezza sulla media dei 4 voti
MODULI = ["3-4-3", "3-5-2", "4-3-3", "4-4-2", "4-5-1", "5-3-2", "5-4-1"]
P_VOTE = {"Titolare": .97, "Probabile titolare": .85, "Titolare (stima)": .75, "In panchina": .3,
          "Riserva (stima)": .2, "In dubbio": .4, "Indisponibile": 0.0, "Infortunato": 0.0, "Squalificato": 0.0,
          "Non convocato": 0.0, "Senza partita": 0.0}


TRANSLIT = str.maketrans({"ø": "o", "Ø": "O", "ð": "d", "Ð": "D", "đ": "d", "Đ": "D", "ł": "l", "Ł": "L", "æ": "ae",
                          "Æ": "AE", "œ": "oe", "Œ": "OE", "ß": "ss", "þ": "th", "Þ": "Th", "ı": "i"})


def norm_tokens(s):
    s = unicodedata.normalize("NFD", (s or "").translate(TRANSLIT)).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z ]+", " ", s).split()


def match_roster_player(entry, cands):
    raw = (entry.get("name") or "").strip()
    toks = norm_tokens(raw)
    initial = None
    if raw.endswith(".") and len(toks) >= 2 and len(toks[-1]) <= 3:
        initial, toks = toks[-1], toks[:-1]
    if not toks:
        return None
    best, bs, n = None, 0.0, len(toks)
    for c in cands:
        ct = norm_tokens(c.get("name"))
        sc = 0.0
        if any(ct[i:i + n] == toks for i in range(len(ct) - n + 1)):
            sc = 10 + (2 if ct[-n:] == toks else 0)
        elif all(t in ct for t in toks):
            sc = 7
        elif any(len(t) >= 4 and t in " ".join(ct) for t in toks):
            sc = 4
        if not sc:
            continue
        if initial:
            sc += 3 if ct and ct[0].startswith(initial) else -4
        sc += min(1.0, (c.get("minutesPlayed") or 0) / 900)
        if sc > bs:
            best, bs = c, sc
    return best if bs >= 6 else None


def _single_projection(A, p, tid, oid, lam_team, lam_opp, ref_f, minutes):
    """Proiezione semplificata per chi non è nell'undici titolare."""
    L, t, o = A["L"], A["T"][tid], A["T"][oid]
    f = minutes / 90
    ratio_ = clamp(lam_team / (t["xgBase"] or L["mu"]), .4, 2.5)
    r = {k: prate(A, p, k) for k in ("expectedGoals", "goals", "expectedAssists", "assists", "fouls", "redCards")}
    g90 = .8 * (r["expectedGoals"] if r["expectedGoals"] is not None else (r["goals"] or 0)) + .2 * (r["goals"] or 0)
    a90 = .8 * (r["expectedAssists"] if r["expectedAssists"] is not None else (r["assists"] or 0)) + .2 * (r["assists"] or 0)
    # giallo come per i titolari (falli per gialli a fallo, quanto difenderà la squadra), senza l'avversario diretto
    if p.get("pos") == "G":
        ly = (prate(A, p, "yellowCards") or 0) * f * ref_f
    else:
        ly = r["fouls"] * f * card_context(A, tid, oid)[0] * card_conv(A, p)[0] * ref_f if r["fouls"] is not None else None
    return {"min": round(minutes), "pGoal": 1 - math.exp(-g90 * f * ratio_) if p.get("pos") != "G" else 0.0,
            "pAssist": 1 - math.exp(-a90 * f * ratio_) if p.get("pos") != "G" else 0.0,
            "pYellow": 1 - math.exp(-ly) if ly is not None else None,
            "pRed": 1 - math.exp(-(r["redCards"] or 0) * f * ref_f),
            "lamG": g90 * f * ratio_, "lamA": a90 * f * ratio_}


def fanta_points(role, st, pr, cs, lam_opp, rating=None, R=FANTA_RULES, votes=None):
    """Punti attesi e voto atteso (senza bonus/malus, serve al modificatore di difesa).
    rating = media voto di Fantacalcio.it, votes = partite a voto: con poche partite pesa poco."""
    pv = P_VOTE.get(st, .5)
    mv = (rating * (votes or 1) + 6.0 * 3) / ((votes or 1) + 3) if rating else 6.0
    vote = R["voto"] + clamp(mv - 6.0, -.7, 1.0)
    if role in ("P", "D"):
        vote += .4 * (cs - .3) - .2 * (lam_opp - 1.3)   # la difesa che tiene alza i voti di portiere e difensori
    lam_g = pr.get("lamG") if pr.get("lamG") is not None else -math.log(1 - min(.99, pr.get("pGoal") or 0))
    lam_a = pr.get("lamA") if pr.get("lamA") is not None else -math.log(1 - min(.99, pr.get("pAssist") or 0))
    pts = (vote + R["gol"] * lam_g + R["assist"] * lam_a + R["ammonizione"] * (pr.get("pYellow") or 0)
           + R["espulsione"] * (pr.get("pRed") or 0))
    if role == "P":
        pts += R["golSubito"] * lam_opp + R["portaInviolata"] * cs
    return pv * pts, pv, vote


def fanta(A, F, data, matches, squads):
    T = A["T"]
    R = dict(FANTA_RULES, **(F.get("rules") or {}))
    tid_by_name = {}
    for tid, t in T.items():
        for nm in (t["team"]["name"], t["team"].get("fullName")):
            tid_by_name[" ".join(norm_tokens(nm))] = tid
    pool = {}
    for pid, x in (squads or {}).items():
        pool[int(pid)] = {"id": int(pid), "name": x.get("name"), "teamId": x.get("teamId"), "pos": x.get("pos"), "minutesPlayed": 0}
    for p in A["players"].values():
        pool[p["id"]] = p
    by_team = {}
    for p in pool.values():
        by_team.setdefault(str(p.get("teamId")), []).append(p)

    # prossima partita di ogni squadra e relativo pronostico
    nxt = {}
    for e in sorted(data.get("live", []) + data.get("next", []), key=lambda e: e["start"]):
        if e.get("status") not in ("notstarted", "inprogress"):
            continue
        for side in ("home", "away"):
            nxt.setdefault(str(e[side]["id"]), (e, side))
    preds = {}

    def pred_for(e):
        if e["id"] not in preds:
            preds[e["id"]] = predict(A, e["home"]["id"], e["away"]["id"], e, matches.get(str(e["id"])))
        return preds[e["id"]]

    out = []
    for team in F.get("teams", []):
        rows = []
        for entry in team.get("players", []):
            key = " ".join(norm_tokens(entry.get("team")))
            tid = tid_by_name.get(key) or next((t for k, t in tid_by_name.items() if key and key in k), None)
            row = {k: entry.get(k) for k in ("name", "role", "team", "q", "fvm", "paid")}
            row.update(teamId=int(tid) if tid else None, id=None, status="Senza partita", pts=0.0, pVote=0.0)
            p = match_roster_player(entry, by_team.get(str(tid), [])) if tid else None
            if p:
                row.update(id=p["id"], fullName=p.get("name"), apps=p.get("appearances"), minSeason=p.get("minutesPlayed"),
                           goals=p.get("goals"), assists=p.get("assists"), rating=p.get("rating"))
            if tid and tid in nxt:
                e, side = nxt[tid]
                P = pred_for(e)
                opp = e["away" if side == "home" else "home"]
                row["next"] = {"eventId": e["id"], "opp": opp, "home": side == "home", "start": e["start"],
                               "round": e.get("round"), "live": e.get("status") == "inprogress"}
                projs = P["players"][side]
                lu = P["lineups"][side]
                lam_team, lam_opp = (P["lh"], P["la"]) if side == "home" else (P["la"], P["lh"])
                cs = P["csH"] if side == "home" else P["csA"]
                pr, st, note = None, None, None
                if p:
                    miss = next((m for m in lu["missing"] if m.get("id") == p["id"]), None)
                    starter = next((x for x in projs if x["id"] == p["id"]), None)
                    bench = any(x.get("id") == p["id"] for x in lu.get("subs") or [])
                    src = lu["source"]
                    if miss:
                        st, note = ("In dubbio" if miss["why"] == "In dubbio" else miss["why"]), miss.get("desc")
                    elif starter:
                        st = "Titolare" if src == "ufficiale" else "Probabile titolare" if src.startswith("probabile") else "Titolare (stima)"
                        pr = starter
                    elif bench:
                        st = "In panchina"
                    elif src == "ufficiale":
                        st = "Non convocato"
                    else:
                        st = "Riserva (stima)"
                    if p["id"] in (lu.get("pct") or {}) and not src == "ufficiale":
                        note = f"{lu['pct'][p['id']]}% di probabilità di giocare secondo Fantacalcio.it" + (f" · {note}" if note else "")
                    if pr is None and st not in ("Indisponibile", "Infortunato", "Squalificato", "Non convocato"):
                        ref_f = (P.get("referee") or {}).get("factor", 1.0)
                        pr = _single_projection(A, dict(p, pos=p.get("pos") or {"P": "G", "D": "D", "C": "M", "A": "F"}.get(entry.get("role"))),
                                                tid, str(opp["id"]), lam_team, lam_opp, ref_f, 45 if st == "In dubbio" else 12)
                else:
                    st, note = "Giocatore non trovato", f"nome o squadra non riconosciuti nelle statistiche di {LEAGUE}"
                pr = pr or {}
                row.update(status=st, note=note, min=pr.get("min"), pGoal=pr.get("pGoal"), pAssist=pr.get("pAssist"),
                           pYellow=pr.get("pYellow"), pCS=cs if entry.get("role") in ("P", "D") else None,
                           xGC=lam_opp if entry.get("role") == "P" else None)
                if p:
                    row["pts"], row["pVote"], row["vote"] = fanta_points(entry.get("role"), st, pr, cs, lam_opp, p.get("rating"), R, p.get("ratingPV"))
            rows.append(row)
        out.append({"league": team.get("league"), "name": team.get("name"), "credits": team.get("credits"),
                    "players": rows, "xi": best_xi(rows, R)})
    return {"teams": out, "rules": R, "modTable": sorted(R.get("modTable") or MOD_TABLE)}


def mod_expected(gk, defs, bands):
    """Valore atteso del modificatore di difesa (portiere + 3 migliori difensori)."""
    votes = sorted([d["vote"] for d in defs if d.get("vote") is not None], reverse=True)[:3]
    if not gk or gk.get("vote") is None or len(votes) < 3:
        return 0.0
    m = (gk["vote"] + sum(votes)) / 4 + (.08 if len(defs) >= 5 else .04)   # si contano i 3 migliori
    phi = lambda x: .5 * (1 + math.erf(x / math.sqrt(2)))
    return sum(b * (phi((hi - m) / MOD_SD) - phi((lo - m) / MOD_SD)) for lo, hi, b in bands)


def best_xi(rows, R=FANTA_RULES):
    """Formazione con più punti attesi (modificatore di difesa compreso) e panchina ordinata per ruolo."""
    by = {r: sorted([x for x in rows if x.get("role") == r], key=lambda x: -(x.get("pts") or 0)) for r in "PDCA"}
    best = None
    for mod in MODULI:
        d, c, a = (int(x) for x in mod.split("-"))
        if len(by["P"]) < 1 or len(by["D"]) < d or len(by["C"]) < c or len(by["A"]) < a:
            continue
        pick = by["P"][:1] + by["D"][:d] + by["C"][:c] + by["A"][:a]
        md = mod_expected(by["P"][0], by["D"][:d], mod_bands(R.get("modTable") or MOD_TABLE)) if R.get("modDifesa") and d >= 4 else 0.0
        tot = sum(x.get("pts") or 0 for x in pick) + md
        if best is None or tot > best["pts"] + 1e-9:
            best = {"formation": mod, "pts": tot, "mod": md, "ids": [x["name"] for x in pick]}
    if best:
        chosen = set(best["ids"])
        # senza switch un titolare assente è sostituito solo da un panchinaro dello stesso ruolo
        best["benchByRole"] = {r: [x["name"] for x in by[r] if x["name"] not in chosen] for r in "PDCA"}
        best["bench"] = [n for r in "PDCA" for n in best["benchByRole"][r]]
    return best

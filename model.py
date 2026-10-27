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
import itertools
import math
import re
import time
import unicodedata

import chicche

K_PRIOR = 12           # peso della stagione scorsa sulle squadre, in partite equivalenti (un buon inizio conta, ma poco)
K_PRIOR_NEW = 6        # con un allenatore nuovo la stagione scorsa pesa meno (confermato dalla prova del 13/10/2026)
# base della forza a inizio stagione: un quarto viene da due stagioni fa (Understat). Prova del 26/10/2026
# (ricerca/prova_stagione.py, cinque campionati maggiori): 1X2 −0,0012 ± 0,0007 sul 2025/26 e −0,0028 ± 0,0022 sul
# 2026/27, in nessun campionato peggio; over/under pari. Dare più peso alla stagione in corso (K_PRIOR 4-8), pesare
# di più la fine della stagione scorsa o avvicinarla alla media peggiora; con 0,15-0,5 il guadagno è simile
PRIOR2_W = 0.25
# Prova all'indietro del 13/10/2026 su 1520 partite (Serie A e Premier 2024/25 e 2025/26, ogni partita prevista solo
# con le precedenti): la forza misurata con gli xG senza rigori (80%) più i gol veri (20%) prevede meglio della vecchia
# formula (55% gol, 45% xG; in difesa tiri in porta e palloni concessi vicino all'area). Correggere per espulsioni,
# punteggio o calci piazzati e per i giocatori in campo non aiuta, o aiuta meno del margine d'errore.
W_GOALS = 0.20
K_STYLE_CUP = 4        # coppa: lo stile nel campionato pesa come 4 partite di coppa (con 8 partite di coppa conta un terzo)
MID_W = 0.25           # cambio di allenatore durante la stagione: le partite prima del cambio (e la stagione scorsa) pesano così
VENUE_W = 0.0          # quota del rendimento in casa/fuori di quest'anno: era 0,20, la prova dice che peggiora (troppo rumoroso)
SOFT_CAP = .10         # tetto di forma, accoppiamenti, stili e ritmo sui gol attesi (dal 14/10/2026 non si applicano più)
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
# in Champions al contrario: meno pareggi con pochi gol. Prova del 26/10/2026 (ricerca/prova_livello_coppa.py) sulle 432
# partite di Champions 2024/25-2026/27: con −0,08 i pareggi previsti erano il 22%, quelli veri il 15% (in tutte e tre
# le stagioni); con +0,05 l'1X2 migliora di 0,0073 ± 0,0026 di log loss, il gol/gol di 0,0013, l'over/under resta
# uguale. Con 0 −0,0049 ± 0,0016, con +0,1 −0,0093 ± 0,0036: si tiene il valore prudente. Nei campionati invece −0,08
# resta il migliore (con 0 l'1X2 peggiora di 0,0011 ± 0,0007, ricerca/prova_stagione.py)
RHO_CUP = 0.05
CALIB = 1.0            # avvicinamento alla media delle forze di attacco e difesa: era 0,80, ma i pronostici risultavano troppo
                       # prudenti (al 74% previsto l'esito usciva l'86% delle volte); con 1,0 sono tarati
FORM_EFF = 0.05        # effetto massimo della forma recente sui gol attesi (dal 14/10/2026 non si applica: vedi predict)
CARD_STYLE_K = .25     # quanto dello scontro di stili va sui cartellini attesi (prova del 14/10/2026: ottimo tra 0,2 e 0,3)
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
    dict(k="recov", c="Difesa", l="Palloni recuperati (Opta)", u="/p", d=1, hi=1,
         f=lambda s, n, c: dv(g(s, "recoveries"), g(s, "optaN") or n), S="Recupera tanti palloni",
         W="Recupera pochi palloni"),
    dict(k="duel", c="Duelli e disciplina", l="Contrasti vinti sul totale", sh="Contrasti vinti (%)", u="%", d=1, hi=1, f=ratio("tacklesWon", "tackles"),
         S="Vince i contrasti", W="Perde i contrasti"),
    dict(k="air", c="Duelli e disciplina", l="Gol di testa subiti", u="/p", d=2, hi=0, f=pm("headedGoalsAgainst"),
         S="Solida sui palloni alti", W="Soffre i colpi di testa"),
    # Opta (Opta Analyst, giocatori sommati per squadra): più affidabili dei contrasti e dei gol di testa subiti
    dict(k="aerial", c="Duelli e disciplina", l="Duelli aerei vinti (Opta)", sh="Duelli aerei vinti (%)", u="%", d=0, hi=1,
         f=ratio("aerialWon", "aerialDuels"), S="Domina nel gioco aereo", W="Perde i duelli aerei"),
    dict(k="ground", c="Duelli e disciplina", l="Duelli a terra vinti (Opta)", sh="Duelli a terra vinti (%)", u="%", d=0, hi=1,
         f=ratio("groundWon", "groundDuels"), S="Vince i duelli a terra", W="Perde i duelli a terra"),
    dict(k="foul", c="Duelli e disciplina", l="Falli commessi", u="/p", d=1, hi=0, f=pm("fouls"), S="Gioco pulito", W="Commette molti falli"),
    dict(k="card", c="Duelli e disciplina", l="Cartellini", u="/p", d=1, hi=0, f=_card, S="Disciplinata", W="Indisciplinata (cartellini)"),
    dict(k="form", c="Rendimento", l="Forma: punti/partita ultime 5", sh="Forma (ultime 5)", u="", d=2, hi=1, f=_form, S="In gran forma", W="Momento negativo"),
    dict(k="home", c="Rendimento", l="Punti/partita in casa", u="", d=2, hi=1, f=_venue("home"), S="Fortino in casa", W="Fragile in casa"),
    dict(k="away", c="Rendimento", l="Punti/partita in trasferta", u="", d=2, hi=1, f=_venue("away"), S="Rende bene in trasferta", W="Fatica in trasferta"),
    dict(k="long", c="Stile", l="Quota di lanci lunghi sul totale dei passaggi", sh="Quota lanci lunghi", u="%", d=1, hi=None, f=ratio("totalLongBalls", "totalPasses")),
    dict(k="press", c="Stile", l="PPDA: passaggi lasciati agli avversari per ogni azione difensiva (più basso = più pressing)", sh="PPDA (pressing)",
         u="", d=1, hi=None, f=plain("ppda")),
    dict(k="fk", c="Stile", l="Falli subiti (punizioni a favore)", sh="Falli subiti", u="/p", d=1, hi=None, f=pm("freeKicks")),
    # baricentro: palloni giocati vicino all'area avversaria (Understat, «deep») o, in Champions, tocchi nell'area avversaria (UEFA)
    dict(k="territory", c="Stile", l="Quota dei palloni giocati vicino alle aree che sono suoi", sh="Baricentro (vicino all'area)", u="%", d=0,
         hi=None, f=lambda s, n, c: dv(g(s, "deep"), (g(s, "deep") or 0) + (g(s, "deepAllowed") or 0), 100) if g(s, "deep") is not None
         else dv(g(s, "uefaBox"), (g(s, "uefaBox") or 0) + (g(s, "uefaBoxA") or 0), 100) if g(s, "uefaBox") is not None else None),
    # Champions: palloni recuperati nella metà campo avversaria (dati ufficiali UEFA), al posto del PPDA che lì non c'è
    dict(k="recohi", c="Stile", l="Palloni recuperati nella metà campo avversaria (UEFA)", sh="Recuperi in avanti", u="/p", d=1, hi=None,
         f=lambda s, n, c: dv(g(s, "uefaReco"), g(s, "uefaN"))),
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


def rating(m, L, npx=None):
    """Forza in attacco e in difesa rispetto alla media (1 = media). npx: (xG senza rigori fatti, concessi) a partita;
    senza (manca Understat) si usa la formula di prima, con tiri in porta e palloni concessi vicino all'area."""
    mu = L["mu"]
    gpm = m.get("gpm") if m.get("gpm") is not None else mu
    xg = m.get("xg") if m.get("xg") is not None else gpm
    gapm = m.get("gapm") if m.get("gapm") is not None else mu
    if npx and npx[0] is not None and npx[1] is not None and L.get("npxg"):
        return {"att": W_GOALS * gpm / mu + (1 - W_GOALS) * npx[0] / L["npxg"],
                "de": W_GOALS * gapm / mu + (1 - W_GOALS) * npx[1] / L["npxg"], "xg": xg}
    sotA = m.get("sotA") if m.get("sotA") is not None else L.get("sotA")
    bcA = m.get("bcA") if m.get("bcA") is not None else L.get("bcA")
    att = (.55 * gpm + .45 * xg) / mu
    # tiri in porta e palloni vicino all'area concessi, quelli che ci sono (nei campionati senza Understat, finché non
    # ci sono i tiri della stagione scorsa, i secondi mancano): con nessuno dei due, solo i gol subiti
    parts = [v / L[k] for v, k in ((sotA, "sotA"), (bcA, "bcA")) if v is not None and L.get(k)]
    de = .55 * gapm / mu + .45 * sum(parts) / len(parts) if parts else gapm / mu
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

    def P2(*ks):   # la prima che c'è: Opta (duelli, recuperi) e, se manca, la misura di prima
        return next((pct[k] for k in ks if pct.get(k) is not None), .5)
    press = (2 * (1 - P("press")) + P2("recov", "rec")) / 3 if pct.get("press") is not None or pct.get("recohi") is None \
        else (2 * P("recohi") + P2("recov", "rec")) / 3   # Champions: recuperi nella metà campo avversaria (UEFA)
    return {
        "possesso": (2 * P("poss") + P("pass")) / 3,
        "baricentro": P("territory"),
        "pressing": press,
        "verticalita": (2 * P("long") + (1 - P("pass"))) / 3,
        "ampiezza": (2 * P("cross") + P("corners")) / 3,
        "transizioni": ((1 - P("poss")) + P("xg")) / 2,   # pericolosa (xG) pur tenendo poco il pallone
        "fisicita": (P2("ground", "duel") + P2("aerial", "air") + (1 - P("foul"))) / 3,
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
    src = t.get("styleSrc")
    if src:   # coppa: stile da campionato + coppa, numeri della sola coppa
        games = lambda k: f"{k} partit{'a' if k == 1 else 'e'}"
        how = (f"stile misurato su {games(src['dom'])} di {src['league']} e {games(src['cup'])} di Champions" if src["dom"]
               else f"stile misurato solo su {games(src['cup'])} di Champions")
        return f"{lead} {a['desc']} ({how})." + (f" In Champions: {', '.join(bits)}." if bits else "")
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
        chips = []   # i gol attesi non si spostano più (prova del 14/10/2026): resta chi è favorito e i cartellini
        if cards and cards * CARD_STYLE_K * 100 >= 1:
            chips.append(f"cartellini +{fmt(cards * CARD_STYLE_K * 100, 0)}%")
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
            ya = Y["pct"].get("aerial", Y["pct"].get("air"))   # duelli aerei vinti (Opta) o, se mancano, gol di testa subiti
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


def npx_of(s, n):
    """xG senza rigori fatti e concessi a partita, dalle statistiche di stagione (Understat)."""
    a, b = num(s.get("npxG")), num(s.get("npxGA"))
    return (a / n, b / n) if a is not None and b is not None and n else None


def build(data, prior=None, matches=None, now=None, coaches=None, role_rows=None, changes=None, us_hist=None, ext=None,
          prior2=None):
    """changes: {squadra: {"at": data dell'ultimo cambio di allenatore in corsa, "pre": cambiato anche d'estate}}; us_hist: {squadra: partite
    di Understat con data, gol e xG senza rigori} (per pesare meno le partite prima del cambio).
    prior2: due stagioni fa, da Understat {squadra: {"G", "GA", "npxG", "npxGA"} a partita, "_lg": medie del campionato}
    (vedi PRIOR2_W).
    ext: forza europea (europa.py, per la Champions) {"mu", "he", "teams": {id: {A, D, league, n}}}: sostituisce la forza
    calcolata dalle partite della competizione, che in coppa sono poche e tra squadre di campionati diversi."""
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
        pn = [(num(s.get("npxG")), int(g(s, "matches") or 0)) for s in prior["teams"].values()]
        pr_league["npxg"] = (sum(a for a, k in pn if a is not None) / sum(k for a, k in pn if a is not None)
                             if any(a is not None and k for a, k in pn) else None)
        for tid, m in pm_.items():
            s_ = prior["teams"][tid]
            pr_rating[tid] = rating(m, pr_league, npx_of(s_, int(g(s_, "matches") or 0)))
        _, ppct, _ = rank_all(pm_)
        for tid in pm_:
            prev_dims[tid] = style_dims(ppct[tid])
            prev_arch[tid] = archetype(prev_dims[tid])["key"]
        # neopromosse: base = media delle ultime 5 della stagione scorsa
        bottom = [str(r["team"]["id"]) for r in sorted(pst.get("total") or [], key=lambda r: -r["pos"])[:5]]
        b = [pr_rating[t] for t in bottom if t in pr_rating]
        if b:
            pr_rating["_promoted"] = {k: mean([x[k] for x in b]) for k in ("att", "de", "xg")}
        # due stagioni fa: un quarto della base, per chi era in campionato in tutte e due (le neopromosse restano come sono)
        lg2 = (prior2 or {}).get("_lg") or {}
        if all(lg2.get(k) for k in ("G", "npxG")):
            for tid, o in prior2.items():
                if tid in pr_rating and tid != "_promoted" and not tid.startswith("_"):
                    att2 = W_GOALS * o["G"] / lg2["G"] + (1 - W_GOALS) * o["npxG"] / lg2["npxG"]
                    de2 = W_GOALS * o["GA"] / lg2["G"] + (1 - W_GOALS) * o["npxGA"] / lg2["npxG"]
                    r_ = pr_rating[tid]
                    pr_rating[tid] = dict(r_, att=(1 - PRIOR2_W) * r_["att"] + PRIOR2_W * att2,
                                          de=(1 - PRIOR2_W) * r_["de"] + PRIOR2_W * de2, two=True)

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
    cn = [(num(x["s"].get("npxG")), x["n"]) for x in T.values()]
    cur_np = sum(a for a, k in cn if a is not None) / sum(k for a, k in cn if a is not None) if any(a is not None for a, k in cn) else None
    pr_np = (pr_league or {}).get("npxg")
    hp = cur["hp"] or 0
    L["npxg"] = (cur_np * hp + pr_np * K_LEAGUE) / (hp + K_LEAGUE) if cur_np and pr_np else cur_np or pr_np
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
        Lr = {"mu": L["mu"], "sotA": cur["sotA"] or L["sotA"], "bcA": cur["bcA"] or L["bcA"], "npxg": L.get("npxg")}
        r = rating(t["m"], Lr, npx_of(t["s"], t["n"]))
        n_eff = t["n"]
        # allenatore cambiato durante la stagione: le partite di prima contano un quarto, e la stagione scorsa ancora meno
        cc, hist = (changes or {}).get(tid) or {}, (us_hist or {}).get(tid) or []
        ch = cc.get("at")
        t["midChange"] = None
        if ch and any(h["t"] < ch for h in hist) and any(h["t"] >= ch for h in hist):
            k_prior = K_PRIOR_NEW if cc.get("pre") else K_PRIOR   # come nella prova: conta il cambio d'estate, non quello in corsa
            ws = [(1.0 if h["t"] >= ch else MID_W, h) for h in hist]
            sw = sum(w_ for w_, _ in ws)
            mm = dict(t["m"], gpm=sum(w_ * h["gf"] for w_, h in ws) / sw, gapm=sum(w_ * h["ga"] for w_, h in ws) / sw)
            r = rating(mm, Lr, (sum(w_ * h["npxg"] for w_, h in ws) / sw, sum(w_ * h["npxga"] for w_, h in ws) / sw))
            n_eff = sw
            k_prior *= MID_W
            t["midChange"] = {"at": ch, "before": sum(1 for h in hist if h["t"] < ch), "after": sum(1 for h in hist if h["t"] >= ch)}
        base = pr_rating.get(tid) or pr_rating.get("_promoted") or dict(NO_PRIOR, xg=L["mu"])
        t["prior"] = "stagione scorsa" if tid in pr_rating else "neopromossa (media delle ultime 5)" if "_promoted" in pr_rating else None
        w = n_eff / (n_eff + k_prior)
        t["att"] = w * r["att"] + (1 - w) * base["att"]
        t["de"] = w * r["de"] + (1 - w) * base["de"]
        t["xgBase"] = w * r["xg"] + (1 - w) * base.get("xg", r["xg"])
        t["priorWeight"] = 1 - w if t["prior"] else 0
        t["priorTwo"] = bool((pr_rating.get(tid) or {}).get("two"))   # base anche da due stagioni fa (PRIOR2_W)
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

    # coppa: attacco e difesa dal modello europeo, riportati alla media delle squadre della competizione (1 = media)
    if ext and ext.get("teams"):
        ids = [tid for tid in T if tid in ext["teams"]]
        if ids:
            ma = mean([ext["teams"][t]["A"] for t in ids])
            md = mean([ext["teams"][t]["D"] for t in ids])
            for tid in ids:
                e = ext["teams"][tid]
                t = T[tid]
                t["att"], t["de"] = math.exp(e["A"] - ma), math.exp(e["D"] - md)
                t["xgBase"] = t["att"] * L["mu"]
                t["prior"], t["priorWeight"] = "forza europea", 1.0
                t["euro"] = {"league": e.get("league"), "n": e.get("n"), "net": round(e["A"] - e["D"], 3)}
                # stile: le poche partite di coppa insieme a quelle del campionato (stesse dimensioni, da 0 a 1)
                dom = e.get("dom")
                if not (dom and dom.get("dims")):   # campionato che l'app non segue: solo le partite di coppa
                    t["styleSrc"] = {"cup": t["n"], "dom": 0, "league": None}
                    t["summary"] = style_summary(t)
                else:
                    w = t["n"] / (t["n"] + K_STYLE_CUP)
                    t["dimsCup"] = t["dims"]
                    t["dims"] = {k: w * v + (1 - w) * dom["dims"].get(k, v) for k, v in t["dims"].items()}
                    t["arch"] = archetype(t["dims"])
                    t["styleSrc"] = {"cup": t["n"], "dom": dom["n"], "league": dom["league"]}
                    t["summary"] = style_summary(t)
            L["HA"] = math.exp(ext["mu"] + ext["he"] + ma + md)
            L["AA"] = math.exp(ext["mu"] + ma + md)
            ranked = sorted(ids, key=lambda t: -(ext["teams"][t]["A"] - ext["teams"][t]["D"]))
            for i, tid in enumerate(ranked):
                T[tid]["euro"]["rank"] = i + 1

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
    return {"T": T, "L": L, "cup": bool(ext and ext.get("teams")), "players": {p["id"]: p for p in players}, "prior_players": prior_players,
            "posavg": posavg, "matches": matches, "hasPrior": bool(pr_rating), "priorYear": (prior or {}).get("year"),
            "priorVol": prior_volume(prior),
            # chicche statistiche delle partite (chicche.py): profili delle squadre, calcolati una volta per analisi
            "chic": chicche.index(data, matches, prior, set(T), bool(ext and ext.get("teams"))),
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
                                 "priorWeight": round(t["priorWeight"], 2), "priorTwo": t.get("priorTwo"), "midChange": t.get("midChange"),
                                 "euro": t.get("euro")},
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


def score_matrix(lh, la, rho=None):
    rho = RHO if rho is None else rho
    ph, pa = pois(lh, MAXG), pois(la, MAXG)
    mat, tot = [], 0.0
    for i in range(MAXG + 1):
        row = []
        for j in range(MAXG + 1):
            tau = 1.0
            if i == 0 and j == 0:
                tau = max(0.0, 1 - lh * la * rho)
            elif i == 0 and j == 1:
                tau = 1 + lh * rho
            elif i == 1 and j == 0:
                tau = 1 + la * rho
            elif i == 1 and j == 1:
                tau = 1 - rho
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
            for k in ("shots", "shotsOnTarget", "corners"):
                tot[f"{side}_{k}"] = tot.get(f"{side}_{k}", 0) + ((b.get(side) or {}).get(k) or 0)
        for p in b["players"].values():
            who = "st" if p.get("start") else "sub"
            for k in ("min", "shots", "sot", "fouls", "fouled", "yc", "goals", "assists"):
                tot[f"{who}_{k}"] = tot.get(f"{who}_{k}", 0) + (p.get(k) or 0)
    if n < 30:
        return {}
    share = {k: tot.get(f"st_{k}", 0) / (tot.get(f"st_{k}", 0) + tot.get(f"sub_{k}", 0))
             for k in ("min", "shots", "sot", "fouls", "fouled", "yc", "goals", "assists") if tot.get(f"st_{k}")}
    vol = {k: {side: tot.get(f"{side}_{k}", 0) / n for side in ("home", "away")} for k in ("shots", "shotsOnTarget", "corners")}
    return {"n": n, "share": share, "teamShots": tot.get("team_shots", 0) / (2 * n), "teamSot": tot.get("team_shotsOnTarget", 0) / (2 * n),
            "vol": vol}


VOL_K = 10                                   # partite della stagione scorsa (o della media) nei volumi di squadra
VOL_SHRINK = {"shots": .85, "shotsOnTarget": .8, "corners": .65}   # quanto resta della distanza dalla media


def prior_volume(prior):
    """Tiri, tiri in porta e angoli fatti e concessi a partita di ogni squadra nella stagione scorsa, rispetto alla
    media di quella stagione: {id: {"shots": 1.12, "shotsA": .9, ...}} (1 = nella media)."""
    teams = (prior or {}).get("teams") or {}
    per = {}
    for tid, st in teams.items():
        n = st.get("matches") or 0
        if n and st.get("shots") is not None:
            per[tid] = {k + a: (st.get(src) or 0) / n for k in ("shots", "shotsOnTarget", "corners")
                        for a, src in (("", k), ("A", k + "Against"))}
    if not per:
        return {}
    avg = {k: sum(x[k] for x in per.values()) / len(per) for k in next(iter(per.values()))}
    return {tid: {k: (v / avg[k] if avg[k] else 1.0) for k, v in x.items()} for tid, x in per.items()}


def team_volume(A, hid, aid, neutral=False):
    """Tiri, tiri in porta e calci d'angolo attesi delle due squadre. Media della lega in casa (o in trasferta) × quanto
    la squadra fa rispetto alla media × quanto l'avversaria concede rispetto alla media; i due rapporti sono
    avvicinati a quelli della stagione scorsa con VOL_K partite (neopromosse e squadre nuove: alla media), poi la
    distanza dalla media si stringe un po' (VOL_SHRINK). Prova all'indietro del 19/10/2026 su 3500 partite dei cinque
    campionati maggiori (ricerca/prova_tiri_angoli.py): errore medio da 3,91 a 3,70 tiri e da 2,21 a 2,14 angoli, e
    le previsioni alte tornano (19,6 tiri previsti contro 19,5 veri; prima oltre 20 previsti erano 15 veri). I fattori
    VOL_SHRINK sono quelli che fanno tornare il 5% delle previsioni più alte e più basse: tiri in porta 6,87 previsti
    contro 6,85 veri, angoli 6,83 contro 6,82 (con 0,87 e 0,75 erano 7,07 contro 6,86 e 7,09 contro 6,77). Prima la
    pagina faceva la media semplice tra quanto fa una squadra e quanto concede l'altra, senza campo né base: con poche
    partite (in Champions due) venivano fuori 24 tiri in trasferta. -> {"shots": [casa, ospiti], ...}"""
    T, L = A["T"], A["L"]
    V = (L.get("shares") or {}).get("vol") or {}
    PV = A.get("priorVol") or {}
    out = {}
    for k in ("shots", "shotsOnTarget", "corners"):
        lg = V.get(k) or {}
        if not lg.get("home") or not lg.get("away"):
            continue
        avg = (lg["home"] + lg["away"]) / 2
        res = []
        for side, t, u in (("home", hid, aid), ("away", aid, hid)):
            ts, us = T[t].get("s") or {}, T[u].get("s") or {}
            nt, nu = T[t].get("n") or 0, T[u].get("n") or 0
            ct = (ts.get(k) or 0) / nt / avg if nt and ts.get(k) is not None else 1.0
            cu = (us.get(k + "Against") or 0) / nu / avg if nu and us.get(k + "Against") is not None else 1.0
            bt, bu = (PV.get(t) or {}).get(k, 1.0), (PV.get(u) or {}).get(k + "A", 1.0)
            at = (nt * ct + VOL_K * bt) / (nt + VOL_K)
            du = (nu * cu + VOL_K * bu) / (nu + VOL_K)
            base = avg if neutral else lg[side]
            res.append(base + VOL_SHRINK[k] * (base * at * du - base))
        out[k] = res
    return out


# ---------- scommesse: le giocate con quota «nella media» (1,35-1,80) e il loro valore ----------

BET_LO, BET_HI = 1.35, 1.80   # fascia chiesta dall'utente (19/10/2026: prima 1,40-1,80, poi «tra 1,35 e 1,70/80»)
# giocate consigliate di ogni partita: una per fascia di quota, da mercati diversi
PICK_TIERS = (("Più sicura", 1.35, 1.50), ("Equilibrata", 1.50, 1.65), ("Quota più alta", 1.65, 1.80))
PICK_FAMILY = {"Esito": "esito", "Doppia chance": "esito", "Pareggio rimborsato": "esito", "Gol": "gol", "Multigol": "gol",
               "Combo": "gol", "Gol squadra": "squadra", "Multigol squadra": "squadra", "Calci d'angolo": "angoli",
               "Tiri in porta": "tiri", "Tiri": "tiri", "Ammonizioni": "cartellini", "Giocatori": "giocatori"}
# a parità di probabilità: prima i mercati che si trovano dappertutto e con la probabilità più provata (esito con le
# quote del mercato, gol, angoli tarati all'indietro), poi tiri e giocatori (il tiro in porta del singolo è stimato
# con una Poisson, che per i giocatori è un po' ottimista)
PICK_PREF = {"esito": 1.0, "gol": 1.0, "squadra": .98, "angoli": .98, "cartellini": .96, "tiri": .94, "giocatori": .85}
# valore delle giocate con la quota vera del bookmaker: la probabilità è per VALUE_W quella del modello e per il resto
# quella del mercato. Prova all'indietro del 19/10/2026 su 3.500 partite (ricerca/prova_valore.py): sull'1X2 il mercato
# prevede meglio del modello (log loss 0,9695 contro 0,9812, e aggiungere il modello non migliora: 0,9700 con peso 0,2) e
# le giocate in cui il solo modello vedeva più del 10% di valore hanno perso tra il 9% e il 16% della posta. Si mostra
# come «con valore» solo da VALUE_MIN in su.
VALUE_W, VALUE_MIN = .2, .03
# dispersione (binomiale negativa, varianza = media + media²/r) stimata il 19/10/2026 su 3500 partite dei cinque
# campionati maggiori (ricerca/prova_mercati.py): con questa le probabilità di over tornano entro 1-3 punti
NB_R = {("shots", 1): 15, ("shots", 2): 50, ("shotsOnTarget", 1): 30, ("shotsOnTarget", 2): 50,
        ("corners", 1): 8, ("corners", 2): 30, ("cards", 1): 1e6, ("cards", 2): 100}
# totali di partita di tiri, tiri in porta e angoli: con la media così com'è gli over uscivano 2-3 punti più spesso del
# previsto (gli under sembravano più sicuri di quanto sono); con la media × 1,02 lo scarto medio della taratura scende
# da 2,3 a 1,1 punti (tiri), da 2,5 a 0,5 (tiri in porta), da 1,4 a 0,7 (angoli). Le squadre e i cartellini tornano già.
TOT_CAL = 1.02


def nb_over(mu, line, r):
    """P(conteggio > line) con media mu e dispersione r (r molto grande = Poisson)."""
    if mu <= 0:
        return 0.0
    k = int(math.floor(line))
    if r >= 1e5:
        return 1 - sum(math.exp(-mu + i * math.log(mu) - math.lgamma(i + 1)) for i in range(k + 1))
    lp = lambda i: math.lgamma(i + r) - math.lgamma(r) - math.lgamma(i + 1) + r * math.log(r / (r + mu)) + i * math.log(mu / (r + mu))
    return 1 - sum(math.exp(lp(i)) for i in range(k + 1))


def picks(items):
    """Le giocate consigliate: per ogni fascia di PICK_TIERS la più probabile (pesata con PICK_PREF), ognuna da un
    mercato diverso. Così non escono tre giocate tutte a 1,40, e chi vuole più quota sa quanto rischia."""
    out, used = [], set()
    for label, lo, hi in PICK_TIERS:
        cands = [it for it in items if lo <= it["fair"] < hi + (1e-9 if hi == BET_HI else 0)
                 and PICK_FAMILY.get(it["g"], it["g"]) not in used]
        if not cands:
            continue
        best = max(cands, key=lambda it: it["p"] * PICK_PREF.get(PICK_FAMILY.get(it["g"], it["g"]), .9))
        used.add(PICK_FAMILY.get(best["g"], best["g"]))
        out.append(dict(best, tier=label))
    return out


def bets(P, names):
    """Le giocate della partita: per ognuna la probabilità e la quota giusta (1/p, la quota minima a cui conviene).
    Dove c'è il mercato (1X2 dai bookmaker; una linea di over/under) la probabilità è per VALUE_W quella del modello e
    per il resto quella del mercato, che prevede meglio (pmod: quella del solo modello, pm: quella del mercato); con
    la quota vera anche il valore = probabilità × quota − 1. Restano quelle con quota giusta tra BET_LO e BET_HI, più
    quelle con valore da VALUE_MIN in su e quota del bookmaker in quella fascia; picks: le tre consigliate.
    names: {"home", "away"} -> nome della squadra."""
    lh, la = P["lh"], P["la"]
    mat = score_matrix(lh, la, RHO_CUP if P.get("cup") else RHO)
    cells = [(i, j, v) for i, row in enumerate(mat) for j, v in enumerate(row)]
    pr = lambda f: sum(v for i, j, v in cells if f(i, j))
    hn, an = names["home"], names["away"]
    out = []

    def add(group, label, p, odds=None, approx=False, pm=None):
        if p <= 0 or p >= 1:
            return
        it = {"g": group, "k": label}
        if pm is not None:   # con il mercato: la probabilità mescolata (quella del solo modello sbaglia di più)
            it.update(pmod=round(p, 4), pm=round(pm, 4))
            p = VALUE_W * p + (1 - VALUE_W) * pm
        it.update(p=round(p, 4), fair=round(1 / p, 2))
        if odds:
            it["odds"] = round(odds, 2)
            it["value"] = round(p * odds - 1, 4)
            if approx:
                it["approx"] = True
        out.append(it)
    M = P.get("market") or {}
    dec = M.get("dec") or []
    mp = [M.get("p1"), M.get("px"), M.get("p2")] if None not in (M.get("p1"), M.get("px"), M.get("p2")) else None
    p1, px, p2 = P["p1"], P["px"], P["p2"]
    # esito, doppia chance, pareggio rimborsato (le quote della doppia chance dal bookmaker sono stimate dall'1X2)
    add("Esito", f"1 · vince {hn}", p1, dec[0] if dec else None, pm=mp and mp[0])
    add("Esito", "X · pareggio", px, dec[1] if dec else None, pm=mp and mp[1])
    add("Esito", f"2 · vince {an}", p2, dec[2] if dec else None, pm=mp and mp[2])
    dc = (lambda a, b: 1 / (1 / dec[a] + 1 / dec[b])) if dec else (lambda a, b: None)
    add("Doppia chance", f"1X · {hn} o pareggio", p1 + px, dc(0, 1), True, pm=mp and mp[0] + mp[1])
    add("Doppia chance", f"X2 · {an} o pareggio", px + p2, dc(1, 2), True, pm=mp and mp[1] + mp[2])
    add("Doppia chance", "12 · non finisce pari", p1 + p2, dc(0, 2), True, pm=mp and mp[0] + mp[2])
    if p1 + p2:
        add("Pareggio rimborsato", f"{hn} (se pari, rimborso)", p1 / (p1 + p2), pm=mp and mp[0] / (mp[0] + mp[2]))
        add("Pareggio rimborsato", f"{an} (se pari, rimborso)", p2 / (p1 + p2), pm=mp and mp[2] / (mp[0] + mp[2]))
    # gol della partita
    ou = M.get("ou") or {}
    # over/under del bookmaker senza il margine
    po_mk = (1 / ou["over"]) / (1 / ou["over"] + 1 / ou["under"]) if ou.get("over") and ou.get("under") else None
    for line in (.5, 1.5, 2.5, 3.5, 4.5):
        po = pr(lambda i, j: i + j > line)
        real = ou.get("line") == line
        add("Gol", f"Over {fmt(line, 1)}", po, ou.get("over") if real else None, pm=po_mk if real else None)
        add("Gol", f"Under {fmt(line, 1)}", 1 - po, ou.get("under") if real else None,
            pm=1 - po_mk if real and po_mk is not None else None)
    for lo, hi in ((0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5), (3, 5)):
        add("Multigol", f"Multigol {lo}-{hi}", pr(lambda i, j: lo <= i + j <= hi))
    gg = pr(lambda i, j: i > 0 and j > 0)
    add("Gol", "Gol (segnano entrambe)", gg)
    add("Gol", "No gol", 1 - gg)
    for side, nm, f in (("home", hn, lambda i, j: i), ("away", an, lambda i, j: j)):
        add("Gol squadra", f"{nm} segna", pr(lambda i, j: f(i, j) > 0))
        add("Gol squadra", f"{nm} over 1,5", pr(lambda i, j: f(i, j) > 1.5))
        add("Gol squadra", f"{nm} under 1,5", pr(lambda i, j: f(i, j) < 1.5))
        add("Multigol squadra", f"Multigol {nm} 1-2", pr(lambda i, j: 1 <= f(i, j) <= 2))
        add("Multigol squadra", f"Multigol {nm} 1-3", pr(lambda i, j: 1 <= f(i, j) <= 3))
    # combo più giocate
    add("Combo", f"1X + over 1,5", pr(lambda i, j: i >= j and i + j > 1.5))
    add("Combo", f"X2 + over 1,5", pr(lambda i, j: j >= i and i + j > 1.5))
    add("Combo", f"1X + under 3,5", pr(lambda i, j: i >= j and i + j < 3.5))
    add("Combo", f"X2 + under 3,5", pr(lambda i, j: j >= i and i + j < 3.5))
    add("Combo", f"1 + over 1,5", pr(lambda i, j: i > j and i + j > 1.5))
    add("Combo", f"2 + over 1,5", pr(lambda i, j: j > i and i + j > 1.5))
    add("Combo", "Gol + over 2,5", pr(lambda i, j: i > 0 and j > 0 and i + j > 2.5))
    # tiri, tiri in porta, calci d'angolo, ammonizioni: linee x,5 attorno alla media
    V = dict(P.get("vol") or {})
    if P.get("cards"):
        V["cards"] = [P["cards"]["home"], P["cards"]["away"]]
    title = {"shots": "Tiri", "shotsOnTarget": "Tiri in porta", "corners": "Calci d'angolo", "cards": "Ammonizioni"}
    for k, (mh, ma) in V.items():
        tot = (mh + ma) * (TOT_CAL if k != "cards" else 1)
        for who, mu, r in (("totali", tot, NB_R[(k, 2)]), (hn, mh, NB_R[(k, 1)]), (an, ma, NB_R[(k, 1)])):
            base = math.floor(mu) + .5
            for line in (base - 2, base - 1, base, base + 1, base + 2):   # le linee che i bookmaker propongono
                if line < .5:
                    continue
                po = nb_over(mu, line, r)
                lab = title[k].lower() if who == "totali" else f"{title[k].lower()} {who}"
                add(title[k], f"Over {fmt(line, 1)} {lab}", po)
                add(title[k], f"Under {fmt(line, 1)} {lab}", 1 - po)
    # giocatori (titolari previsti): segna, almeno un tiro in porta
    for side in ("home", "away"):
        for q in (P.get("players") or {}).get(side) or []:
            if q.get("pos") == "G":
                continue
            if q.get("pGoal"):
                add("Giocatori", f"{q['name']} segna", q["pGoal"])
            if q.get("sot"):
                add("Giocatori", f"{q['name']} almeno 1 tiro in porta", 1 - math.exp(-q["sot"]))
    keep = [it for it in out if BET_LO <= it["fair"] <= BET_HI or (it.get("value", -1) >= VALUE_MIN and BET_LO <= it.get("odds", 0) <= BET_HI)]
    keep.sort(key=lambda it: -it["p"])
    return {"lo": BET_LO, "hi": BET_HI, "vmin": VALUE_MIN, "vw": VALUE_W, "items": keep,
            "picks": picks([it for it in keep if BET_LO <= it["fair"] <= BET_HI]), "n": len(out)}


# ---------- MyCombo: tre combinazioni di giocate sulla stessa partita (Serie A e Premier) ----------

# Chieste dall'utente il 27/10/2026: per ogni partita di Serie A e Premier tre MyCombo di Sisal (più giocate della
# stessa partita, una quota sola) vicine a quota 10, 15 e 20, fatte solo di giocate che il modello dà come probabili,
# con i mercati che Sisal offre nelle MyCombo: esito, gol, gol di squadra, multigol, giocatori «o chi entra al suo
# posto» (segna, segna o fa assist, tiri, tiri in porta), tiri e tiri in porta, angoli (anche «in entrambi i tempi»),
# punti cartellini di squadra e della partita. Mai statistiche dei giocatori senza il sostituto né cartellini dei
# singoli (richiesta dell'utente). Le quote di Sisal non si leggono in automatico (la loro API risponde 403 ai
# programmi): la quota della combo si stima con COMBO_Q e COMBO_K, misurati componendo combo vere su Sisal.
COMBO_LEAGUES = ("Serie A", "Premier League")
COMBO_TARGETS = (10, 15, 20)
COMBO_TOL = .10                      # quota stimata entro il 10% dall'obiettivo
# giocate probabili, ma non quasi certe (sotto 1,10 alzano poco la quota). Dal 27/10 sera niente giocate sotto il 65%
# per arrivare alla quota (richiesta dell'utente: «leva giocate più difficili e poco probabili»; al 70% non si arriva
# a 15 e 20 in quasi nessuna partita)
COMBO_PMIN, COMBO_PMAX = .65, .92
# (probabilità minima, giocate sui giocatori solo se alzano la quota di COMBO_BOOST): se a una quota non si arriva, si
# accettano prima i tiri che la alzano poco, poi giocate fino al 62%, mai sotto
COMBO_PSTEPS = ((.65, True), (.65, False), (.62, False))
# Quanto Sisal fa pagare ogni tipo di giocata rispetto al modello: (1 / quota Sisal) / probabilità del modello, mediana
# sulle giocate tra 50% e 95% di 5 partite di Serie A lette il 27/10/2026 (n tra 4 e 61 per tipo). I tiri dei
# giocatori sono i più cari (1,20: Sisal li paga come se uscissero il 20% più spesso di quanto dice il modello, che
# su questi è tarato entro 2-4 punti), i punti cartellini i più giusti (1,01).
COMBO_Q = {"esito": 1.04, "gol": 1.06, "gg": 1.10, "golsq": 1.08, "angoli": 1.07, "angoliET": 1.03, "angoli2": 1.10,
           "porta": 1.07, "portaET": 1.09, "porta2": 1.05, "tiri": 1.07, "cart": 1.01, "cart2": 1.14,
           "gioc_gol": 1.03, "gioc_tiri": 1.20, "gioc_tiri2": 1.20 ** 2}
# Quota MyCombo di Sisal = prodotto delle quote stimate delle giocate (1 / (p × COMBO_Q), mai sotto 1,02), diviso per
# il legame tra le giocate sui gol (probabilità insieme dalla matrice / prodotto delle singole: Sisal le valuta
# insieme), × COMBO_K. Sui tiri dei giocatori Sisal non sconta il legame (Venezia-Inter con 15 giocate, quasi tutte
# tiri dell'Inter: 19,16 contro 15,54 del prodotto delle quote singole). Nelle 8 combo composte il 27/10/2026 la
# MyCombo vale da 0,89 a 1,51 volte il prodotto delle quote vere; con le quote stimate K va da 0,67 a 1,16 per le combo
# di giocate probabili (Milan-Bologna, Frosinone-Lecce, Genoa-Juventus, Monza-Napoli, Venezia-Inter con 8 e 15
# giocate) e arriva a 1,8-2,2 dove il modello vede le giocate molto più probabili di Sisal (Parma-Udinese,
# Fiorentina-Atalanta). La stima sbaglia quindi di ±30%: la quota vera si vede componendo la combo.
COMBO_K = .9
# Tiri dei giocatori per alzare la quota, soprattutto della squadra favorita (richiesta dell'utente del 27/10 sera,
# come nelle sue schedine): fino a COMBO_PLAYERS giocatori, per ognuno «almeno n tiri», «almeno n tiri in porta» o le
# due insieme (probabilità calcolata insieme: i tiri in porta sono una parte dei tiri). Nella scelta ogni loro giocata vale
# COMBO_FAV in più se il giocatore è della favorita (COMBO_BOTH se non c'è una favorita netta, COMBO_OTHER se è
# dell'altra squadra). Favorita: probabilità di vittoria del pronostico più 0,03 per ogni chiave tattica («forze contro
# debolezze») che vince, con almeno COMBO_FAV_GAP di distacco.
COMBO_PLAYERS = 10
COMBO_FAV, COMBO_BOTH, COMBO_OTHER, COMBO_FAV_GAP = .3, .2, .05, .05
COMBO_BOOST = 1.05                   # quota stimata minima di una giocata su un giocatore (1,10 per tiri + tiri in porta)
COMBO_GOALS = 3                      # giocate sui gol (esito, gol, gol di squadra) in una combo, al massimo
# tiri del giocatore «o chi entra al suo posto»: chi entra tira come lui, dispersione 5. Prova del 27/10/2026 sulle 61
# partite con formazione ufficiale dello storico di Serie A e Premier (1.120 titolari, 422 sostituiti, ritrovati 500
# cambi su 513): tra previsto e vero 2-4 punti di scarto medio per «almeno 1, 2, 3 tiri», 4 per i tiri in porta
COMBO_SUB, COMBO_R_PLAYER = 1.0, 5
COMBO_H1 = .45                       # quota del primo tempo di tiri in porta e angoli
# tiri e tiri in porta di una squadra secondo i gol che segna, rispetto alla sua media (1.136 partite-squadra di 7
# campionati, 2026/27, misurate il 27/10/2026): 0 gol × 0,92 e × 0,72, 1 gol 0,97 e 0,93, 2 gol 1,02 e 1,10, 3 gol
# 1,06 e 1,20, 4 o più 1,17 e 1,39. Nelle combo legano i tiri (soprattutto in porta) all'esito e ai gol.
COMBO_GOAL_SHOTS = (.92, .97, 1.02, 1.06, 1.17)
COMBO_GOAL_SOT = (.72, .93, 1.10, 1.20, 1.39)


def pois_ge(mu, k):
    """P(conteggio di Poisson con media mu almeno k)."""
    return 1 - sum(math.exp(-mu) * mu ** i / math.factorial(i) for i in range(k)) if mu > 0 else 0.0


def combo_inputs(lh, la, vol, cards, rho):
    """Quello che serve alle giocate di una partita: matrice dei risultati, tiri, tiri in porta, angoli e gialli attesi."""
    mat = score_matrix(lh, la, rho)
    return {"cells": [(i, j, v) for i, row in enumerate(mat) for j, v in enumerate(row) if v > 1e-9], "lh": lh, "la": la,
            "vol": vol, "cards": cards}


def combo_prob(spec, X):
    """Probabilità di una giocata (spec) con gli ingressi X di combo_inputs."""
    kind = spec[0]
    if kind == "goal":
        return sum(v for i, j, v in X["cells"] if spec[1](i, j))
    if kind == "nb":     # tiri, tiri in porta, angoli: della partita (t) o di una squadra, sopra o sotto la linea
        _, k, who, line, over = spec
        mh, ma = X["vol"][k]
        mu, r = ((mh + ma) * TOT_CAL, NB_R[(k, 2)]) if who == "t" else (mh if who == "h" else ma, NB_R[(k, 1)])
        po = nb_over(mu, line, r)
        return po if over else 1 - po
    if kind == "et":     # almeno n in entrambi i tempi
        _, k, who, n = spec
        mh, ma = X["vol"][k]
        mu, r = ((mh + ma) * TOT_CAL, NB_R[(k, 2)]) if who == "t" else (mh if who == "h" else ma, NB_R[(k, 1)])
        return nb_over(mu * COMBO_H1, n - .5, r) * nb_over(mu * (1 - COMBO_H1), n - .5, r)
    if kind == "both":   # entrambe le squadre almeno n
        _, k, n = spec
        mh, ma = X["vol"][k]
        return nb_over(mh, n - .5, NB_R[(k, 1)]) * nb_over(ma, n - .5, NB_R[(k, 1)])
    ch, ca = X["cards"][0] + .07, X["cards"][1] + .07   # punti cartellini: gialli più un po' di rossi (valgono 2)
    if kind == "cards":
        _, who, line, over = spec
        po = nb_over(ch + ca, line, NB_R[("cards", 2)]) if who == "t" else nb_over(ch if who == "h" else ca, line, NB_R[("cards", 1)])
        return po if over else 1 - po
    if kind == "bothcards":
        return pois_ge(ch, spec[1]) * pois_ge(ca, spec[1])
    raise ValueError(kind)


def nb_pmf(mu, n, r):
    """P(conteggio = n) per una binomiale negativa con media mu e dispersione r."""
    return math.exp(math.lgamma(n + r) - math.lgamma(r) - math.lgamma(n + 1) + r * math.log(r / (r + mu)) + n * math.log(mu / (r + mu)))


def binom_ge(n, p, k):
    """P(binomiale(n, p) almeno k)."""
    if k <= 0:
        return 1.0
    if n < k:
        return 0.0
    return 1 - sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k))


def combo_goals(P):
    """Gol attesi per le combo: quelli del pronostico avvicinati alle quote del mercato come per le giocate singole
    (VALUE_W al modello, il resto al mercato) quando ci sono: 1X2 e la linea di over/under dei bookmaker. Il pronostico
    resta quello del solo modello. -> (gol attesi casa, ospite, True se c'era il mercato)"""
    M = P.get("market") or {}
    if None in (M.get("p1"), M.get("px"), M.get("p2")):
        return P["lh"], P["la"], False
    rho = RHO_CUP if P.get("cup") else RHO

    def probs(lh, la):
        mat = score_matrix(lh, la, rho)
        cells = [(i, j, v) for i, row in enumerate(mat) for j, v in enumerate(row)]
        return cells, sum(v for i, j, v in cells if i > j), sum(v for i, j, v in cells if i < j)
    t1 = VALUE_W * P["p1"] + (1 - VALUE_W) * M["p1"]
    t2 = VALUE_W * P["p2"] + (1 - VALUE_W) * M["p2"]
    ou = M.get("ou") or {}
    tov = line = None
    if ou.get("over") and ou.get("under") and ou.get("line"):
        line = ou["line"]
        pmk = (1 / ou["over"]) / (1 / ou["over"] + 1 / ou["under"])
        cells, _, _ = probs(P["lh"], P["la"])
        tov = VALUE_W * sum(v for i, j, v in cells if i + j > line) + (1 - VALUE_W) * pmk

    def err(lh, la):
        cells, p1, p2 = probs(lh, la)
        e = (p1 - t1) ** 2 + (p2 - t2) ** 2
        if tov is not None:
            e += (sum(v for i, j, v in cells if i + j > line) - tov) ** 2
        return e
    best = (err(P["lh"], P["la"]), P["lh"], P["la"])
    for span in (.5, .12, .03):   # griglia sempre più fine attorno al migliore
        _, h0, a0 = best
        for dh in range(-5, 6):
            for da in range(-5, 6):
                lh, la = h0 * (1 + span * dh / 5), a0 * (1 + span * da / 5)
                if lh > .05 and la > .05:
                    e = err(lh, la)
                    if e < best[0]:
                        best = (e, lh, la)
    return best[1], best[2], True


def combo_full(X, legs, NMAX=45):
    """Probabilità che escano tutte le giocate di una combo. Gol, esito e marcatori dalla matrice dei risultati (i gol
    della squadra divisi tra i giocatori). Per ogni squadra, i tiri dei suoi giocatori e i suoi tiri e tiri in porta
    sono parti dei tiri della squadra (binomiale negativa, NB_R), che a loro volta crescono con i gol che segna
    (COMBO_GOAL_SHOTS, COMBO_GOAL_SOT): così escono più spesso insieme tra loro e con i gol. Ogni giocata resta con la
    sua probabilità tarata; il resto è indipendente."""
    gl = [l["spec"][1] for l in legs if l["spec"][0] == "goal"]
    pl = [l["ply"] for l in legs if l.get("ply")]
    cells = X["cells"]
    T = {}
    for si, side in ((0, "home"), (1, "away")):
        mu = X["vol"]["shots"][si]
        th_t = min(X["vol"]["shotsOnTarget"][si] / mu, 1.0) if mu else 0
        fns = []
        for l in legs:
            s = l["spec"]
            if s[0] in ("pnb", "pair") and l.get("side") == side and mu:
                if s[0] == "pnb":
                    sh, n_, sot = min(s[1] / mu, 1.0), s[2], s[3] == "sot"
                    fns.append(lambda N, rk, sh=sh, n_=n_, sot=sot: binom_ge(N, min(sh * (rk if sot else 1), 1.0), n_))
                else:
                    _, ls, th, a, b = s
                    sh = min(ls / mu, 1.0)
                    fns.append(lambda N, rk, sh=sh, th=th, a=a, b=b: sum(
                        math.comb(N, m) * sh ** m * (1 - sh) ** (N - m) * binom_ge(m, min(th * rk, 1.0), b) for m in range(a, N + 1)))
            elif s[0] == "nb" and s[2] == ("h" if si == 0 else "a") and s[4] and s[1] in ("shots", "shotsOnTarget"):
                if s[1] == "shots":
                    fns.append(lambda N, rk, L=s[3]: 1.0 if N > L else 0.0)
                else:
                    fns.append(lambda N, rk, L=s[3]: binom_ge(N, min(th_t * rk, 1.0), int(L) + 1))
        if not fns:
            continue
        pk = [0.0] * 5
        for i, j, v in cells:
            pk[min(i if si == 0 else j, 4)] += v
        ns = sum(p * f for p, f in zip(pk, COMBO_GOAL_SHOTS)) or 1
        no = sum(p * f for p, f in zip(pk, COMBO_GOAL_SOT)) or 1
        cond, marg = [], [0.0] * len(fns)
        for k in range(5):
            fs, fo = COMBO_GOAL_SHOTS[k] / ns, COMBO_GOAL_SOT[k] / no
            pm = [nb_pmf(mu * fs, N, NB_R[("shots", 1)]) for N in range(NMAX + 1)]
            vals = [[fn(N, fo / fs) for N in range(NMAX + 1)] for fn in fns]
            cond.append(sum(pm[N] * math.prod(v[N] for v in vals) for N in range(NMAX + 1)))
            for t, v in enumerate(vals):
                marg[t] += pk[k] * sum(pm[N] * v[N] for N in range(NMAX + 1))
        mm = math.prod(marg)
        T[si] = [c / mm if mm > 0 else 1.0 for c in cond]
    tot = 0.0
    for i, j, v in cells:
        if not all(f(i, j) for f in gl):
            continue
        for side, k in (("home", i), ("away", j)):
            ss = [s for sd, s in pl if sd == side]
            if len(ss) == 1:
                v *= 1 - (1 - ss[0]) ** k
            elif len(ss) == 2:
                v *= 1 - (1 - ss[0]) ** k - (1 - ss[1]) ** k + max(0.0, 1 - ss[0] - ss[1]) ** k
        for si, k in ((0, i), (1, j)):
            if si in T:
                v *= T[si][min(k, 4)]
        tot += v
    for l in legs:
        if l["spec"][0] not in ("goal", "ply"):
            tot *= l["p"]
    return min(tot, 1.0)


def pair_prob(ls, th, a, b):
    """P(il giocatore fa almeno a tiri e almeno b tiri in porta): tiri binomiale negativa (media ls, COMBO_R_PLAYER),
    ognuno in porta con probabilità th."""
    tot = 0.0
    for n in range(a, 41):
        pin = 1 - (1 - th) ** n if b == 1 else 1 - (1 - th) ** n - n * th * (1 - th) ** (n - 1)
        tot += nb_pmf(ls, n, COMBO_R_PLAYER) * pin
    return tot


def combo_legs(P, names, X):
    """Tutte le giocate possibili della partita: {g: gruppo (una per gruppo in una combo), k: testo, spec, ply,
    q: quanto Sisal la fa pagare rispetto al modello (COMBO_Q), c: come si controlla sul risultato (combo_check; una
    coppia tiri + tiri in porta ne ha due)}."""
    hn, an = names["home"], names["away"]
    L = []

    def add(g, k, spec, c, ply=None, q=None, side=None):
        L.append({"g": g, "k": k, "spec": spec, "c": c, "ply": ply, "q": COMBO_Q[q or g], "side": side})
    for k, key, f in ((f"1 · vince {hn}", "1", lambda i, j: i > j), ("X · pareggio", "X", lambda i, j: i == j),
                      (f"2 · vince {an}", "2", lambda i, j: i < j), (f"1X · {hn} o pareggio", "1X", lambda i, j: i >= j),
                      (f"X2 · {an} o pareggio", "X2", lambda i, j: i <= j), ("12 · non finisce pari", "12", lambda i, j: i != j)):
        add("esito", k, ("goal", f), ["esito", key])
    for line in (1.5, 2.5, 3.5, 4.5):
        add("gol", f"Over {fmt(line, 1)}", ("goal", lambda i, j, l=line: i + j > l), ["tot", line, "o"])
        add("gol", f"Under {fmt(line, 1)}", ("goal", lambda i, j, l=line: i + j < l), ["tot", line, "u"])
    for lo, hi in ((1, 3), (1, 4), (2, 4), (2, 5), (3, 5)):
        add("gol", f"Multigol {lo}-{hi}", ("goal", lambda i, j, lo=lo, hi=hi: lo <= i + j <= hi), ["mg", "t", lo, hi])
    add("gg", "Goal · segnano entrambe", ("goal", lambda i, j: i > 0 and j > 0), ["gg", 1])
    add("gg", "NoGoal · almeno una non segna", ("goal", lambda i, j: i == 0 or j == 0), ["gg", 0])
    for side, nm in (("h", hn), ("a", an)):
        sg = (lambda i, j: i) if side == "h" else (lambda i, j: j)
        for line in (.5, 1.5, 2.5):
            add("gol" + side, f"{nm} over {fmt(line, 1)} gol", ("goal", lambda i, j, l=line, sg=sg: sg(i, j) > l),
                ["sq", side, line, "o"], q="golsq")
            add("gol" + side, f"{nm} under {fmt(line, 1)} gol", ("goal", lambda i, j, l=line, sg=sg: sg(i, j) < l),
                ["sq", side, line, "u"], q="golsq")
        for lo, hi in ((1, 2), (1, 3), (2, 4)):
            add("gol" + side, f"Multigol {nm} {lo}-{hi}", ("goal", lambda i, j, lo=lo, hi=hi, sg=sg: lo <= sg(i, j) <= hi),
                ["mg", side, lo, hi], q="golsq")
    # tiri e tiri in porta (Sisal nelle MyCombo ha solo gli over), angoli: linee x,5 attorno alla media
    title = {"shots": ("tiri", "tiri"), "shotsOnTarget": ("porta", "tiri in porta"), "corners": ("angoli", "angoli")}
    for k, (g, t) in title.items():
        mh, ma = X["vol"][k]
        for who, mu, nm in (("t", (mh + ma) * TOT_CAL, ""), ("h", mh, " " + hn), ("a", ma, " " + an)):
            base = math.floor(mu) + .5
            for line in (base - 2, base - 1, base, base + 1, base + 2):
                if line < .5:
                    continue
                add(g, f"Over {fmt(line, 1)} {t}{nm}", ("nb", k, who, line, True), ["nb", k, who, line, 1])
                if k == "corners":
                    add(g, f"Under {fmt(line, 1)} {t}{nm}", ("nb", k, who, line, False), ["nb", k, who, line, 0])
    # niente angoli «in entrambi i tempi»: ESPN non dà gli angoli per tempo, e una combo che non si può controllare sul
    # risultato non serve a verificare il modello (i tiri in porta per tempo invece vengono dalla cronaca)
    for who, nm in (("h", hn), ("a", an)):
        for n in (1, 2):
            add("porta", f"{nm} almeno {n} tir{'o' if n == 1 else 'i'} in porta in entrambi i tempi", ("et", "shotsOnTarget", who, n),
                ["et", "shotsOnTarget", who, n], q="portaET")
    for n in (2, 3, 4):
        add("angoli", f"Entrambe almeno {n} angoli", ("both", "corners", n), ["both", "corners", n], q="angoli2")
        add("porta", f"Entrambe almeno {n} tiri in porta", ("both", "shotsOnTarget", n), ["both", "shotsOnTarget", n], q="porta2")
    ch, ca = X["cards"]
    for who, mu, nm in (("t", ch + ca + .14, ""), ("h", ch + .07, " " + hn), ("a", ca + .07, " " + an)):
        for line in (math.floor(mu) - .5, math.floor(mu) + .5, math.floor(mu) + 1.5):
            if line < .5:
                continue
            add("cart", f"Over {fmt(line, 1)} punti cartellini{nm}", ("cards", who, line, True), ["cards", who, line, 1])
            add("cart", f"Under {fmt(line, 1)} punti cartellini{nm}", ("cards", who, line, False), ["cards", who, line, 0])
    for n in (1, 2):
        add("cart", f"Entrambe almeno {n} punt{'o' if n == 1 else 'i'} cartellini", ("bothcards", n), ["bothcards", n], q="cart2")
    # giocatori titolari previsti, «o chi entra al suo posto»: per i minuti che restano tira e segna come lui. La loro
    # quota dei gol è rispetto ai gol attesi del pronostico (le combo possono spostare quelli della squadra)
    for side, lam_t in (("home", P["lh"]), ("away", P["la"])):
        for q in (P.get("players") or {}).get(side) or []:
            if q.get("pos") == "G" or not q.get("min"):
                continue
            f90 = 1 + (90 / q["min"] - 1) * COMBO_SUB
            nm, g, pid = q["name"], f"pl{q['id']}", q["id"]
            lg, la_ = (q.get("lamG") or 0) * f90, (q.get("lamA") or 0) * f90
            if lg:
                add(g, f"{nm} (o chi entra al suo posto) segna", ("ply",), ["ply", pid, "g"], ply=(side, min(lg / lam_t, .95)),
                    q="gioc_gol", side=side)
            if lg + la_:
                add(g, f"{nm} (o chi entra al suo posto) segna o fa assist", ("ply",), ["ply", pid, "ga"],
                    ply=(side, min((lg + la_) / lam_t, .95)), q="gioc_gol", side=side)
            for n in (1, 2, 3, 4):
                if q.get("shots"):
                    add(g, f"{nm} (o chi entra al suo posto) almeno {n} tir{'o' if n == 1 else 'i'}", ("pnb", q["shots"] * f90, n, "shots"),
                        ["pl", pid, "shots", n], q="gioc_tiri", side=side)
            for n in (1, 2):
                if q.get("sot"):
                    add(g, f"{nm} (o chi entra al suo posto) almeno {n} tir{'o' if n == 1 else 'i'} in porta",
                        ("pnb", q["sot"] * f90, n, "sot"), ["pl", pid, "sot", n], q="gioc_tiri", side=side)
            if q.get("shots") and q.get("sot"):
                ls, th = q["shots"] * f90, min(q["sot"] / q["shots"], 1.0)
                for a in (2, 3, 4):
                    for b in (1, 2):
                        if b < a:
                            add(g, [f"{nm} (o chi entra al suo posto) almeno {a} tiri",
                                    f"{nm} (o chi entra al suo posto) almeno {b} tir{'o' if b == 1 else 'i'} in porta"],
                                ("pair", ls, th, a, b), [["pl", pid, "shots", a], ["pl", pid, "sot", b]], q="gioc_tiri2", side=side)
    return L


def combo_joint(X, legs):
    """Probabilità che escano tutte: gol, esito e giocatori che segnano dalla matrice dei risultati (i gol della squadra
    divisi tra i giocatori secondo la loro quota); tiri, angoli e cartellini indipendenti tra loro e dai gol (per
    combinazioni di soli over la probabilità vera è un po' più alta: stima prudente)."""
    gl = [l["spec"][1] for l in legs if l["spec"][0] == "goal"]
    pl = [l["ply"] for l in legs if l.get("ply")]
    tot = 0.0
    for i, j, v in X["cells"]:
        if not all(f(i, j) for f in gl):
            continue
        for side, k in (("home", i), ("away", j)):
            ss = [s for sd, s in pl if sd == side]
            if len(ss) == 1:
                v *= 1 - (1 - ss[0]) ** k
            elif len(ss) == 2:
                v *= 1 - (1 - ss[0]) ** k - (1 - ss[1]) ** k + max(0.0, 1 - ss[0] - ss[1]) ** k
        tot += v
    for l in legs:
        if l["spec"][0] not in ("goal", "ply"):
            tot *= l["p"]
    return tot


def mycombo(A, P, names):
    """Tre combo per la partita, vicine alle quote COMBO_TARGETS su Sisal. Quota stimata di una combo = prodotto delle
    quote stimate delle sue giocate (1 / (probabilità del modello × COMBO_Q), mai sotto 1,02) × COMBO_K: Sisal non
    sconta le giocate legate tra loro. Probabilità della combo (combo_full): gol, esito e marcatori dalla matrice dei
    risultati con i gol avvicinati al mercato (combo_goals), i tiri della stessa squadra legati tra loro e ai suoi gol,
    il resto indipendente. Ogni giocata tra
    COMBO_PMIN e COMBO_PMAX; c'è sempre almeno una giocata sui gol o sull'esito e almeno un giocatore. Tra le combo
    vicine alla quota si sceglie quella con le giocate più probabili, usando i tiri dei giocatori (soprattutto della
    squadra favorita) per alzare la quota, e a parità quella con le giocate più legate a questa partita (probabilità
    contro quella di una partita qualunque della lega); la seconda e la terza riusano il meno possibile le giocate
    delle precedenti."""
    rho = RHO_CUP if P.get("cup") else RHO
    vol = {k: [P["vol"][k][0], P["vol"][k][1]] for k in ("shots", "shotsOnTarget", "corners")}
    lh_c, la_c, with_mk = combo_goals(P)
    X = combo_inputs(lh_c, la_c, vol, [P["cards"]["home"], P["cards"]["away"]], rho)
    Lg = A["L"]
    V0 = (Lg.get("shares") or {}).get("vol") or {}
    vol0 = {k: [(V0.get(k) or {}).get("home") or vol[k][0], (V0.get(k) or {}).get("away") or vol[k][1]] for k in vol}
    X0 = combo_inputs(Lg.get("HA") or P["lh"], Lg.get("AA") or P["la"], vol0, [Lg.get("yellow") or X["cards"][0]] * 2, rho)
    # squadra favorita: probabilità di vittoria del pronostico e chiavi tattiche vinte («forze contro debolezze»)
    ins = P.get("ins") or []
    sc = {s: P[pk] + .03 * sum(1 for i in ins if str(i.get("winner")) == str(P[s])) for s, pk in (("home", "p1"), ("away", "p2"))}
    fav = ("home" if sc["home"] - sc["away"] >= COMBO_FAV_GAP else "away" if sc["away"] - sc["home"] >= COMBO_FAV_GAP
           else None)
    odds1 = lambda p, q: max(1.02, 1 / (p * q))   # quota stimata su Sisal di una giocata
    legs = []
    for l in combo_legs(P, names, X):
        s = l["spec"]
        if s[0] == "ply":
            l["p"] = combo_joint(X, [l])
            p0 = l["p"]
        elif s[0] == "pnb":
            l["p"] = nb_over(s[1], s[2] - .5, COMBO_R_PLAYER)
            p0 = l["p"]
        elif s[0] == "pair":
            _, ls, th, a, b = s
            l["p"] = pair_prob(ls, th, a, b)
            l["parts"] = [nb_over(ls, a - .5, COMBO_R_PLAYER), nb_over(ls * th, b - .5, COMBO_R_PLAYER)]
            p0 = l["p"]
        else:
            l["p"], p0 = combo_prob(s, X), combo_prob(s, X0)
        pmin_all = min(p for p, _ in COMBO_PSTEPS)
        if not (pmin_all <= l["p"] <= COMBO_PMAX) or (s[0] == "pair" and min(l["parts"]) < pmin_all):
            continue
        # peso nella quota: log della quota stimata (le due giocate di una coppia ognuna con la sua)
        l["w"] = (sum(math.log(odds1(p, COMBO_Q["gioc_tiri"])) for p in l["parts"]) if s[0] == "pair"
                  else math.log(odds1(l["p"], l["q"])))
        # i tiri dei giocatori servono ad alzare la quota: quelli che la alzano meno di COMBO_BOOST (quasi certi, su Sisal
        # a 1,02-1,04) tolgono probabilità senza dare niente, e si usano solo se non c'è altro modo
        l["weak"] = bool(l.get("side")) and l["w"] < math.log(COMBO_BOOST) * (2 if s[0] == "pair" else 1)
        # valore nella combo: la probabilità (per intero), più un premio ai tiri dei giocatori della favorita, che
        # così sono il primo modo per arrivare alla quota; un poco quanto la giocata è legata a questa partita
        bonus = (COMBO_BOTH if fav is None else COMBO_FAV if l["side"] == fav else COMBO_OTHER) if l.get("side") else 0.0
        bonus *= 2 if s[0] == "pair" else 1   # due giocate su Sisal
        l["v"] = math.log(l["p"]) + bonus + .1 * math.log(l["p"] / clamp(p0, .01, .99))
        legs.append(l)
    GOAL = ("esito", "gol", "gg", "golh", "gola")
    STEP = .02
    NB_ = int(math.log(max(COMBO_TARGETS) * 1.3) / STEP) + 2
    REUSE = .05    # giocata già in una combo precedente della stessa partita

    def goal_sets(goal):
        """Gruppi di giocate sui gol: da 1 a COMBO_GOALS gruppi diversi, al massimo un giocatore (segna o fa assist)."""
        out_, byg = [], {}
        for l in goal:
            byg.setdefault(l["g"], []).append(l)
        for n in range(1, COMBO_GOALS + 1):
            for groups in itertools.combinations(list(byg), n):
                if sum(1 for g in groups if g.startswith("pl")) > 1:
                    continue
                for c in itertools.product(*(byg[g] for g in groups)):
                    pj = combo_joint(X, list(c))
                    if pj > 0:
                        out_.append((c, pj))
        return out_

    def dp(stat, exclude, used):
        """Zaino a gruppi sulle statistiche: per ogni somma dei pesi nella quota (passi di STEP) e numero di
        giocatori, la scelta con il valore più alto."""
        groups = {}
        for l in stat:
            if l["g"] not in exclude:
                groups.setdefault(l["g"], []).append(l)
        best = {(0, 0): (0.0, ())}
        for g, items in groups.items():
            isp = g.startswith("pl")
            new = dict(best)
            for (b, k), (v, ch) in best.items():
                for l in items:
                    nb = b + int(round(l["w"] / STEP))
                    nk = k + isp
                    if nb >= NB_ or nk > COMBO_PLAYERS:
                        continue
                    nv = v + l["v"] - (REUSE if id(l) in used else 0)
                    if (nb, nk) not in new or nv > new[(nb, nk)][0]:
                        new[(nb, nk)] = (nv, ch + (l,))
            best = new
        return best

    def search(target, gsets, stat, used):
        """La combo con il valore più alto tra quelle con quota stimata entro COMBO_TOL da exp(target)."""
        cache, cand = {}, None
        for need_player in (True, False):
            for c, pj in gsets:
                pls = frozenset(l["g"] for l in c if l["g"].startswith("pl"))
                if pls not in cache:
                    cache[pls] = dp(stat, pls, used)
                best = cache[pls]
                vg = sum(l["v"] - (REUSE if id(l) in used else 0) for l in c)
                # Sisal conta il legame tra le giocate sui gol (più probabili insieme, quota più bassa): lo stesso con
                # la matrice dei risultati
                wg = sum(l["w"] for l in c) - math.log(pj / math.prod(l["p"] for l in c))
                # solo i passi dello zaino vicini alla quota cercata (la somma arrotondata sbaglia di qualche passo)
                lo, hi = int((target - wg - tol) / STEP) - 3, int((target - wg + tol) / STEP) + 3
                for b in range(max(lo, 0), min(hi, NB_ - 1) + 1):
                    for k in range(COMBO_PLAYERS + 1):
                        e = best.get((b, k))
                        if not e or (need_player and not (k or pls)):
                            continue
                        v, ch = e
                        if cand is not None and vg + v <= cand[0]:
                            continue
                        lw = wg + sum(l["w"] for l in ch)
                        if abs(lw - target) <= tol:
                            cand = (vg + v, c + ch, pj * math.prod(l["p"] for l in ch), math.exp(lw) * COMBO_K)
            if cand:
                return cand
        return None
    out, used = [], set()
    tol = math.log(1 + COMBO_TOL)
    pools = {}
    for T in COMBO_TARGETS:
        target = math.log(T / COMBO_K)
        cand = None
        for step in COMBO_PSTEPS:
            pmin, boost = step
            if step not in pools:
                ok = [l for l in legs if l["p"] >= pmin and (l["spec"][0] != "pair" or min(l["parts"]) >= pmin)
                      and not (boost and l["weak"])]
                goal = [l for l in ok if l["g"] in GOAL or l["spec"][0] == "ply"]
                pools[step] = (goal_sets(goal), [l for l in ok if l not in goal])
            gsets, stat = pools[step]
            cand = search(target, gsets, stat, used)
            if cand:
                break
        if not cand:
            continue
        _, chosen, pj, est = cand
        pj = combo_full(X, chosen)   # i tiri della stessa squadra escono più spesso insieme, e con i suoi gol
        used |= {id(l) for l in chosen}
        out.append({"t": T, "p": round(pj, 4), "fair": round(1 / pj, 2), "est": round(est, 1), "ev": round(pj * est - 1, 3),
                    "legs": [{"k": k, "p": round(p, 3), "c": c} for l in sorted(chosen, key=lambda l: -l["p"])
                             for k, p, c in (zip(l["k"], l["parts"], l["c"]) if l["spec"][0] == "pair" else [(l["k"], l["p"], l["c"])])]})
    return {"k": COMBO_K, "pmin": COMBO_PMIN, "fav": names[fav] if fav else None, "mk": with_mk, "items": out}


# ---------- partite più gustose: divario ampio, una squadra top e una flop, giocate in fascia con valore ----------

GUSTO_MIN_N = 3                  # partite di entrambe per usare i numeri della stagione (in coppa a ottobre sono 2)
GUSTO_TOP, GUSTO_FLOP = .7, .3   # percentile: nel 30% migliore e nel 30% peggiore della lega


def _elide(k):
    """Ordinali che cominciano per vocale (8, 11, 80-89): «l'8ª», «l'11° attacco»."""
    return k in (8, 11) or 80 <= k < 90


def _att(r, N):
    if r == 1:
        return "il miglior attacco"
    k, w = (r, "miglior attacco") if r <= (N + 1) / 2 else (N - r + 1, "attacco più debole")
    if k == 1:
        return "l'attacco più debole"
    return f"{'l' + chr(39) if _elide(k) else 'il '}{k}° {w}"


def _def(r, N):
    if r == 1:
        return "la miglior difesa"
    k, w = (r, "miglior difesa") if r <= (N + 1) / 2 else (N - r + 1, "difesa più debole")
    if k == 1:
        return "la difesa più debole"
    return f"{'l' + chr(39) if _elide(k) else 'la '}{k}ª {w}"


def _place(T, tid, key, low_first=False):
    """«la più alta», «la 2ª più alta», «l'8ª più bassa, a pari con altre 3»: il valore della squadra tra quelli della
    lega, contato dal lato più vicino (a pari valore non si dà un posto finto). low_first: per le voci in cui la migliore
    è la più bassa (gol e xG concessi)."""
    vals = [T[t]["m"].get(key) for t in T if T[t]["m"].get(key) is not None]
    v = T[tid]["m"][key]
    better = sum(1 for x in vals if (x < v if low_first else x > v))
    worse = sum(1 for x in vals if (x > v if low_first else x < v))
    ties = len(vals) - 1 - better - worse
    top, bottom = ("bassa", "alta") if low_first else ("alta", "bassa")
    k, w = (better + 1, top) if better <= worse else (worse + 1, bottom)
    txt = f"la più {w}" if k == 1 else f"{'l' + chr(39) if _elide(k) else 'la '}{k}ª più {w}"
    if ties:
        txt += ", a pari con un'altra" if ties == 1 else f", a pari con altre {ties}"
    return txt


def gustose(items, A, pos=None, n=6, days=8):
    """Le partite più «gustose» dei prossimi giorni (richiesta dell'utente del 19/10/2026): divario ampio secondo il
    pronostico, la favorita tra le migliori della lega e l'avversaria tra le peggiori nelle stesse voci, e le giocate tra
    BET_LO e BET_HI, con il valore dove c'è la quota vera del bookmaker. items: [(partita ESPN, pronostico)]; pos:
    {squadra: posizione in classifica}. Voci a confronto: forza del modello (attacco contro difesa e viceversa), e con
    almeno GUSTO_MIN_N partite xG creati contro concessi, punti in casa contro punti fuori, forma, classifica.
    Il divario è la probabilità della favorita mescolata a quella dei bookmaker quando c'è (VALUE_W: sull'1X2 il
    mercato prevede meglio). Punteggio 0-100: 55% il divario (favorita dal 45% all'80%), 45% i contrasti top/flop
    (quattro valgono il massimo); il valore non entra nel punteggio perché, provato all'indietro, quello del modello
    contro il mercato non regge. Entrano le partite con la favorita almeno al 55% e almeno due contrasti top/flop, o
    la favorita almeno al 65%."""
    if not items:
        return []
    first = min(e["start"] for e, P in items)
    T = A["T"]
    N = len(T)
    att_rank = {t: i + 1 for i, t in enumerate(sorted(T, key=lambda t: -T[t]["att"]))}
    de_rank = {t: i + 1 for i, t in enumerate(sorted(T, key=lambda t: T[t]["de"]))}
    pr = lambda r: 1 - (r - 1) / (N - 1) if N > 1 else .5
    out = []
    for e, P in items:
        if e["start"] - first > days * 86400:
            continue
        M = P.get("market") or {}
        p1, p2 = P["p1"], P["p2"]
        if M.get("p1") is not None and M.get("p2") is not None:   # la stima migliore: modello mescolato al mercato
            p1, p2 = VALUE_W * p1 + (1 - VALUE_W) * M["p1"], VALUE_W * p2 + (1 - VALUE_W) * M["p2"]
        fs, ds = ("home", "away") if p1 >= p2 else ("away", "home")
        pb = max(p1, p2)
        pf = P["p1"] if fs == "home" else P["p2"]
        pm = M.get("p1" if fs == "home" else "p2")
        tf, td = str(e[fs]["id"]), str(e[ds]["id"])
        if tf not in T or td not in T:
            continue
        F, G = T[tf], T[td]
        fn, dn = F["team"]["name"], G["team"]["name"]
        rows = []

        def add(text, pa, pb):
            rows.append({"t": text, "tf": pa >= GUSTO_TOP and pb <= GUSTO_FLOP, "d": round(pa - pb, 3)})
        add(f"Attacco contro difesa: secondo il modello {fn} ha {_att(att_rank[tf], N)}, {dn} {_def(de_rank[td], N)}.",
            pr(att_rank[tf]), pr(de_rank[td]))
        add(f"Difesa contro attacco: secondo il modello {fn} ha {_def(de_rank[tf], N)}, {dn} {_att(att_rank[td], N)}.",
            pr(de_rank[tf]), pr(att_rank[td]))
        if min(F.get("n") or 0, G.get("n") or 0) >= GUSTO_MIN_N:
            fm, gm, fp, gp = F["m"], G["m"], F["pct"], G["pct"]
            ok = lambda *ks: all(fm.get(k) is not None and gm.get(k) is not None and fp.get(k) is not None
                                 and gp.get(k) is not None for k in ks)
            pl = lambda tid, k, low=False: _place(T, tid, k, low)
            if ok("xg", "xga"):
                add(f"In questa stagione {fn} crea {fmt(fm['xg'], 2)} xG a partita ({pl(tf, 'xg')}), {dn} ne concede "
                    f"{fmt(gm['xga'], 2)} ({pl(td, 'xga', True)}).", fp["xg"], gp["xga"])
                add(f"In questa stagione {fn} concede {fmt(fm['xga'], 2)} xG a partita ({pl(tf, 'xga', True)}), {dn} ne crea "
                    f"{fmt(gm['xg'], 2)} ({pl(td, 'xg')}).", fp["xga"], gp["xg"])
            kf, kd = ("home", "away") if fs == "home" else ("away", "home")
            if ok(kf, kd):
                where = {"home": "in casa", "away": "in trasferta"}
                add(f"{fn} {where[kf]} fa {fmt(fm[kf], 2)} punti a partita ({pl(tf, kf)}), {dn} {where[kd]} "
                    f"{fmt(gm[kd], 2)} ({pl(td, kd)}).", fp[kf], gp[kd])
            if ok("form"):
                add(f"Nelle ultime cinque {fn} ha fatto {fmt(fm['form'], 1)} punti a partita, {dn} {fmt(gm['form'], 1)}.",
                    fp["form"], gp["form"])
            if pos and pos.get(tf) and pos.get(td):
                add(f"In classifica {fn} è {pos[tf]}ª, {dn} {pos[td]}ª su {N}.", pr(pos[tf]), pr(pos[td]))
        ntf = sum(1 for r in rows if r["tf"])
        if pb < .55 or (ntf < 2 and pb < .65):
            continue
        items_b = (P.get("bets") or {}).get("items") or []
        val = sorted((it for it in items_b if it.get("value", -1) >= VALUE_MIN and BET_LO <= it.get("odds", 0) <= BET_HI),
                     key=lambda it: -it["value"])[:3]
        top = (P.get("bets") or {}).get("picks") or []
        score = 100 * (.55 * clamp((pb - .45) / .35, 0, 1) + .45 * min(1, ntf / 4))
        # modello e bookmaker: d'accordo, o il mercato vede la partita più equilibrata (e di solito ha ragione)
        mk = None
        if pm is not None:
            if pf - pm >= .1:
                mk = ("I bookmaker la vedono più equilibrata del modello: sull'1X2 il mercato di solito prevede meglio, "
                      "quindi il divario va preso con cautela.")
            elif pm - pf >= .1:
                mk = f"I bookmaker sono ancora più sicuri del modello sulla vittoria di {fn}."
            elif abs(pf - pm) <= .05:
                mk = "Modello e bookmaker sono d'accordo sulla favorita."
        good = sorted((r for r in rows if r["d"] >= .3), key=lambda r: -r["d"])
        warn = min((r for r in rows if r["d"] <= -.3), key=lambda r: r["d"], default=None)
        out.append({"id": e["id"], "start": e["start"], "home": str(e["home"]["id"]), "away": str(e["away"]["id"]),
                    "fav": fs, "pf": round(pf, 3), "pm": round(pm, 3) if pm else None, "pb": round(pb, 3), "mk": mk,
                    "src": M.get("src"),
                    "lh": round(P["lh"], 2), "la": round(P["la"], 2), "score": round(score), "ntf": ntf, "nrows": len(rows),
                    "why": [{"t": r["t"], "tf": r["tf"]} for r in good[:4]], "warn": warn["t"] if warn else None,
                    "value": val, "top": top, "odds": bool(M.get("dec"))})
    # le n con il punteggio più alto, mostrate in ordine di data (richiesta dell'utente del 20/10/2026)
    return sorted(sorted(out, key=lambda g: -g["score"])[:n], key=lambda g: g["start"])


def start_share(A, projs, key, default=.88):
    """Quota della statistica che fanno i titolari in questa partita: quella reale della lega, più alta o più bassa se
    i titolari previsti giocano più o meno minuti dei titolari di solito."""
    S = (A["L"].get("shares") or {}).get("share") or {}
    if key not in S or "min" not in S:
        return min(default, sum(p["min"] for p in projs) / 990)
    return clamp(S[key] * sum(p["min"] for p in projs) / (990 * S["min"]), .55, .97)


def anchor_team(A, projs, tid, oid, lam_team, vol=None):
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
    # tiri e tiri in porta della squadra in questa partita: quelli di team_volume (campo, avversaria, stagione scorsa),
    # gli stessi che la pagina mostra; i titolari se ne prendono la loro quota
    if vol and vol.get("shots"):
        targets["shots"] = vol["shots"] * sh["shots"]
        if vol.get("shotsOnTarget"):
            targets["sot"] = vol["shotsOnTarget"] * sh["sot"]
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
    # portiere: pesa solo se al suo posto gioca un vero secondo. Con i portieri che si alternano (Monza 2026/27: Thiam,
    # Törnqvist e Pizzignacco titolari 3, 2 e 1 volta) chi entra gioca comunque spesso e la difesa non perde niente
    gk_in = [pid for pid in starters if (sh.get(pid) or {}).get("pos") == "G"]
    regular_in = any((sh.get(pid) or {}).get("min", 0) >= .3 for pid in gk_in)
    for x in out:
        if x["pos"] == "G" and regular_in:
            x["gkSub"] = True
    att = min(.3, sum(x["w"] * x["att"] * .45 for x in out))
    de = min(.2, sum(x["w"] * x["def"] * .35 for x in out) + sum(.06 * x["w"] for x in out if x["pos"] == "G" and not x.get("gkSub")))
    return out, att, de


def referee_factor(A, ref):
    if not ref or not ref.get("games"):
        return 1.0, None
    ypg = ((ref.get("yellow") or 0) + (ref.get("yellowRed") or 0)) / ref["games"]
    base = ref.get("base") or A["L"]["yellowGame"]   # media delle stesse partite da cui viene il suo dato
    rel = ypg / base if base else 1
    w = ref["games"] / (ref["games"] + 10)
    return clamp(w * rel + (1 - w), .75, 1.3), ypg


def predict(A, hid, aid, ev=None, extra=None, combos=False):
    """combos: anche le tre MyCombo (solo Serie A e Premier; le calcolano la pagina della partita e il sito, non i
    giri su tutte le partite, perché costano qualche decimo di secondo l'una)."""
    hid, aid = str(hid), str(aid)
    T, L = A["T"], A["L"]
    H, Aw = T[hid], T[aid]
    adj = []

    def shr(r, n, k):
        return (n * r + k) / (n + k)

    attH, deH, attA, deA = (x ** CALIB for x in (H["att"], H["de"], Aw["att"], Aw["de"]))
    cup = A.get("cup")
    neutral = bool((ev or {}).get("neutral"))   # finale in campo neutro: nessun vantaggio del campo
    hr, ar = H["ctx"]["home"], Aw["ctx"]["away"]
    if VENUE_W and hr and hr.get("p"):
        attH = (1 - VENUE_W) * attH + VENUE_W * shr(hr["gf"] / hr["p"] / L["HA"], hr["p"], 4)
        deH = (1 - VENUE_W) * deH + VENUE_W * shr(hr["ga"] / hr["p"] / L["AA"], hr["p"], 4)
    if VENUE_W and ar and ar.get("p"):
        attA = (1 - VENUE_W) * attA + VENUE_W * shr(ar["gf"] / ar["p"] / L["AA"], ar["p"], 4)
        deA = (1 - VENUE_W) * deA + VENUE_W * shr(ar["ga"] / ar["p"] / L["HA"], ar["p"], 4)
    lh, la = (L["AA"] if neutral else L["HA"]) * attH * deA, L["AA"] * attA * deH
    base_h, base_a = lh, la

    # forma, accoppiamenti tattici, scontro di stili e ritmo: provati all'indietro il 14/10/2026 su 3503 partite dei
    # cinque campionati maggiori (2024/25 e 2025/26, ricerca/prova_correzioni.py), con le stesse funzioni e i dati fino
    # al giorno prima. Nessuno migliora il pronostico (log loss dell'1X2 da +0,0000 a +0,0005, tutti insieme +0,0013 ±
    # 0,0012) e accoppiamenti, stili e ritmo peggiorano un po' l'over/under. Restano come descrizioni (chiavi tattiche,
    # scontro di stili, forma) ma non spostano i gol attesi, come già in coppa. I cartellini dello scontro di stili sì,
    # ma a un quarto (CARD_STYLE_K): con l'effetto pieno 4,38 gialli previsti contro 4,04 veri (3,90 senza).
    ins = sorted(insights(H, Aw, "h", L["N"]) + insights(Aw, H, "a", L["N"]), key=lambda i: -i["score"])
    clash = style_clash(H, Aw, A)
    clash = dict(clash, eff={"h": 0.0, "a": 0.0}, tempo=0.0, cards=0.0 if cup else clash["cards"] * CARD_STYLE_K)

    # formazioni e assenti
    lu = (extra or {}).get("lineups")
    confirmed = bool(lu and lu.get("confirmed"))
    sides = {"h": (lu or {}).get("home"), "a": (lu or {}).get("away")}
    # assenze: spostano i gol attesi da una squadra all'altra senza cambiarne il totale (prova del 14/10/2026: così
    # l'1X2 migliora, −0,0032 ± 0,0015 dalla 6ª giornata, e l'over/under resta com'è; con il totale libero peggiorava).
    # Nel «perché»: una frase completa per ogni motivo, sotto la squadra i cui gol attesi cambiano, poi il riequilibrio
    absent, fac, parts = {}, {"h": 1.0, "a": 1.0}, {"h": [], "a": []}

    def names_of(lst, keep):
        ns = [x["name"] for x in lst if keep(x) and x.get("name")]
        return ", ".join(ns[:-1]) + " e " + ns[-1] if len(ns) > 1 else (ns[0] if ns else "alcuni titolari")
    for key, tid, oppkey in (("h", hid, "a"), ("a", aid, "h")):
        lst, att_loss, def_loss = absences(A, tid, sides[key], confirmed)
        absent[key] = lst
        who = T[tid]["team"]["name"]
        if att_loss:
            fac[key] *= 1 - att_loss
            parts[key].append((f"{who} senza {names_of(lst, lambda x: x['att'] >= .05)} in attacco", -att_loss * 100))
        if def_loss:
            fac[oppkey] *= 1 + def_loss
            parts[oppkey].append((f"{who} senza {names_of(lst, lambda x: x['def'] >= .05 or (x['pos'] == 'G' and not x.get('gkSub')))} in difesa",
                                  def_loss * 100))
    if fac["h"] != 1.0 or fac["a"] != 1.0:
        k = (lh + la) / (lh * fac["h"] + la * fac["a"])
        for key, tid in (("h", hid), ("a", aid)):
            for text, pct in parts[key]:
                adj.append({"team": int(tid), "what": text, "pct": pct})
            if abs(k - 1) >= .0005:
                adj.append({"team": int(tid), "what": "Riequilibrio: le assenze spostano i gol attesi tra le due squadre, "
                            "il totale della partita resta quello di prima", "pct": (k - 1) * 100})
        lh, la = lh * fac["h"] * k, la * fac["a"] * k
    lh, la = clamp(lh, .2, 4.5), clamp(la, .2, 4.5)

    mat = score_matrix(lh, la, RHO_CUP if cup else RHO)
    res, scores = outcome_probs(mat)
    tie = tie_probs(mat, lh, la, (ev or {}).get("tie")) if cup and (ev or {}).get("tie") else None
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
    vol = team_volume(A, hid, aid, neutral)
    side_vol = lambda i: {k: v[i] for k, v in vol.items()}
    anchor_team(A, proj_h, hid, aid, lh, side_vol(0))
    anchor_team(A, proj_a, aid, hid, la, side_vol(1))
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

    out = {
        "home": int(hid), "away": int(aid), "eventId": (ev or {}).get("id"), "start": (ev or {}).get("start"),
        "round": (ev or {}).get("round"), "lh": lh, "la": la, "baseH": base_h, "baseA": base_a, **res,
        "scores": scores[:8], "mat": [row[:6] for row in mat[:6]], "pick": pick,
        "top": {"i": scores[0]["i"], "j": scores[0]["j"], "p": scores[0]["v"]},
        "ins": ins[:8], "adj": adj, "absent": {"home": absent["h"], "away": absent["a"]},
        "lineups": {"confirmed": confirmed, "home": side_out("h", hid), "away": side_out("a", aid)},
        "players": {"home": proj_h, "away": proj_a},
        "cards": {"home": cards_h, "away": cards_a},
        "vol": vol,   # tiri, tiri in porta e angoli attesi delle due squadre (team_volume)
        "yellowRisk": yellow,
        "referee": dict(ref, ypg=ref_ypg, factor=ref_f) if ref else None,
        "style": {"home": {"arch": H["arch"], "dims": H["dims"], "coach": H["coach"]},
                  "away": {"arch": Aw["arch"], "dims": Aw["dims"], "coach": Aw["coach"]},
                  "items": clash["items"], "tempo": clash["tempo"], "cards": clash["cards"], "poss": clash["poss"],
                  "matches": A.get("archMatches", 0)},
        "h2h": (extra or {}).get("h2h"), "tie": tie, "neutral": neutral, "cup": bool(cup),
        "market": market_of(extra),   # quote dei bookmaker senza il margine, per il confronto
        "coachRoles": {"home": (H.get("coachRoles") or {}).get("text"), "away": (Aw.get("coachRoles") or {}).get("text")},
        "prior": {"home": H["prior"], "away": Aw["prior"], "weightH": H["priorWeight"], "weightA": Aw["priorWeight"],
                  "year": A["priorYear"]},
    }
    # scommesse: le giocate con quota «nella media» e il loro valore (in fondo alla pagina della partita)
    out["bets"] = bets(out, {"home": H["team"]["name"], "away": Aw["team"]["name"]})
    if combos and LEAGUE in COMBO_LEAGUES and not cup:
        try:
            out["mycombo"] = mycombo(A, out, {"home": H["team"]["name"], "away": Aw["team"]["name"]})
        except Exception as e:
            out["mycombo"], out["mycomboErr"] = None, f"{type(e).__name__}: {e}"
    # chicche statistiche, dalla più particolare alla più semplice (sopra le scommesse); un errore qui non deve
    # fermare il pronostico
    try:
        out["chicche"] = chicche.match_facts(A, hid, aid, extra, LEAGUE)
    except Exception as e:
        out["chicche"], out["chiccheErr"] = [], f"{type(e).__name__}: {e}"
    return out


def tie_probs(mat, lh, la, tie):
    """Coppa: probabilità di passare il turno. tie: {"first": [gol dell'andata della squadra di casa di oggi, gol
    dell'ospite di oggi]} (finale: [0, 0]). Pareggio nel totale: supplementari (gol attesi per 30 minuti) e poi rigori
    a sorte."""
    f = tie.get("first") or [0, 0]
    ph = 0.0
    xh, xa = pois(lh / 3, MAXG), pois(la / 3, MAXG)
    et_h = sum(xh[i] * xa[j] for i in range(MAXG + 1) for j in range(MAXG + 1) if i > j)
    et_d = sum(xh[i] * xa[i] for i in range(MAXG + 1))
    for i, row in enumerate(mat):
        for j, v in enumerate(row):
            gh, ga = f[0] + i, f[1] + j
            ph += v if gh > ga else v * (et_h + et_d / 2) if gh == ga else 0.0
    return {"home": ph, "away": 1 - ph, "first": f, "final": bool(tie.get("final"))}


def base_lambdas(A, hid, aid, neutral=False):
    """Gol attesi di base (solo la forza delle squadre), per simulare le partite lontane (proiezione della classifica)."""
    H, Aw, L = A["T"][str(hid)], A["T"][str(aid)], A["L"]
    attH, deH, attA, deA = (x ** CALIB for x in (H["att"], H["de"], Aw["att"], Aw["de"]))
    return (L["AA"] if neutral else L["HA"]) * attH * deA, L["AA"] * attA * deH


def summary(P):
    return {k: P[k] for k in ("p1", "px", "p2", "lh", "la", "over25", "btts", "pick", "top")} | {
        "lineups": "ufficiale" if P["lineups"]["confirmed"] else P["lineups"]["home"]["source"],
        "picks": [{k: it.get(k) for k in ("tier", "g", "k", "p", "fair", "odds", "value")} for it in (P.get("bets") or {}).get("picks") or []]}


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
        P = predict(A, e["home"]["id"], e["away"]["id"], e, matches.get(str(e["id"])), combos=True)
        it = items.setdefault(str(e["id"]), {"id": e["id"], "round": e.get("round"), "start": e["start"],
                                            "home": e["home"], "away": e["away"]})
        it["start"] = e["start"]
        it["latest"] = dict(summary(P), at=now, pl=history_players(P), cards=[round(P["cards"]["home"], 2),
                            round(P["cards"]["away"], 2)], ref=(P.get("referee") or {}).get("name"))
        if (P.get("mycombo") or {}).get("items"):   # le MyCombo, da controllare sul risultato (combo_eval)
            it["latest"]["combo"] = [{"t": c["t"], "p": c["p"], "est": c["est"], "legs": [[l["k"], l["p"], l["c"]] for l in c["legs"]]}
                                     for c in P["mycombo"]["items"]]
        mk = market_of(matches.get(str(e["id"])))
        if mk:
            it["latestMk"] = mk
        changed = True
    for eid, it in items.items():
        if "final" not in it and it.get("latest") and now >= it["start"]:
            it["final"] = it["latest"]
            if it.get("latestMk"):   # le quote al fischio d'inizio, accanto al pronostico
                it["market"] = it["latestMk"]
            changed = True
    for e in data.get("played") or []:
        it = items.get(str(e["id"]))
        if it and it.get("final") and "result" not in it and e.get("hs") is not None:
            it["result"] = {"hs": e["hs"], "as": e["as"]}
            it["eval"] = evaluate(it["final"], e["hs"], e["as"])
            changed = True
        # il mercato sulla stessa partita (quote di chiusura, se al fischio non c'erano): stesso metro del pronostico
        if it and it.get("result") and "evalMk" not in it:
            mk = it.get("market") or market_of(matches.get(str(e["id"])))
            if mk:
                it["market"] = mk
                it["evalMk"] = evaluate_probs(mk, e["hs"], e["as"])
                changed = True
    # le statistiche vere dei giocatori (ESPN) arrivano poco dopo il risultato
    for eid, it in items.items():
        box = (matches.get(eid) or {}).get("box")
        if it.get("result") and "real" not in it and box and box.get("players"):
            it["real"] = history_real(box, ids)
            changed = True
        if it.get("real") and (it.get("final") or {}).get("combo") and "comboEval" not in it and box:
            it["comboEval"] = combo_eval(it, matches.get(eid) or {})
            changed = True
    return changed


def combo_eval(it, x):
    """Le MyCombo salvate contro la partita vera: per ogni giocata True (uscita), False o None (non si può
    controllare: angoli per tempo, giocatore che non ha giocato), e la combo uscita solo se escono tutte."""
    hs, as_ = it["result"]["hs"], it["result"]["as"]
    box, real = x.get("box") or {}, (it.get("real") or {}).get("players") or {}
    L = x.get("lineups") or {}
    ev = (x.get("ev") or {}).get("ev") or []
    norm = lambda s: re.sub(r"[^a-z]", "", unicodedata.normalize("NFKD", s or "").encode("ascii", "ignore").decode().lower())
    # chi è entrato al posto di ogni titolare (cronaca ESPN e panchina della formazione)
    repl = {}
    for e in ev:
        if e.get("k") != "sub":
            continue
        side = e.get("s")
        st = {norm(p.get("name")): p.get("id") for p in ((L.get(side) or {}).get("starters") or [])}
        sb = {norm(p.get("name")): p.get("id") for p in ((L.get(side) or {}).get("subs") or [])}
        o, w = norm(e.get("o")), norm(e.get("w"))
        po = st.get(o) or next((v for k, v in st.items() if o and (k.endswith(o[-6:]) or o.endswith(k[-6:]))), None)
        pw = sb.get(w) or next((v for k, v in sb.items() if w and (k.endswith(w[-6:]) or w.endswith(k[-6:]))), None)
        if po is not None and pw is not None:
            repl[str(po)] = str(pw)

    def duo(pid, idx):
        r = real.get(str(pid))
        if not r or not r[1]:
            return None
        v = r[idx] or 0
        s = real.get(repl.get(str(pid), ""))
        return v + ((s[idx] or 0) if s else 0)
    team = lambda side, k: (box.get(side) or {}).get(k)
    pts = lambda side: None if team(side, "yellowCards") is None else (team(side, "yellowCards") or 0) + (team(side, "redCards") or 0)
    sides = {"h": "home", "a": "away"}

    def stat(kind, who):
        if who == "t":
            a, b = team("home", kind), team("away", kind)
            return None if a is None or b is None else a + b
        return team(sides[who], kind)

    def chk(c):
        t = c[0]
        if t == "esito":
            o = "1" if hs > as_ else "X" if hs == as_ else "2"
            return o in c[1]
        if t == "tot":
            return hs + as_ > c[1] if c[2] == "o" else hs + as_ < c[1]
        if t == "mg":
            g = hs + as_ if c[1] == "t" else hs if c[1] == "h" else as_
            return c[2] <= g <= c[3]
        if t == "gg":
            return (hs > 0 and as_ > 0) == bool(c[1])
        if t == "sq":
            g = hs if c[1] == "h" else as_
            return g > c[2] if c[3] == "o" else g < c[2]
        if t == "nb":
            v = stat(c[1], c[2])
            return None if v is None else (v > c[3]) == bool(c[4])
        if t == "both":
            a, b = team("home", c[1]), team("away", c[1])
            return None if a is None or b is None else a >= c[2] and b >= c[2]
        if t == "cards":
            v = (None if pts("home") is None or pts("away") is None else pts("home") + pts("away")) if c[1] == "t" else pts(sides[c[1]])
            return None if v is None else (v > c[2]) == bool(c[3])
        if t == "bothcards":
            a, b = pts("home"), pts("away")
            return None if a is None or b is None else a >= c[1] and b >= c[1]
        if t == "et" and c[1] == "shotsOnTarget":   # tiri in porta per tempo dalla cronaca (parate e gol)
            side = sides[c[2]]
            n = [0, 0]
            for e in ev:
                if e.get("s") == side and (e.get("k") == "goal" or (e.get("k") == "shot" and e.get("r") == "saved")) and e.get("p") in (1, 2):
                    n[e["p"] - 1] += 1
            return n[0] >= c[3] and n[1] >= c[3] if ev else None
        if t == "pl":
            v = duo(c[1], 2 if c[2] == "shots" else 3)
            return None if v is None else v >= c[3]
        if t == "ply":
            g = duo(c[1], 6)
            if g is None:
                return None
            return g >= 1 or (c[2] == "ga" and (duo(c[1], 7) or 0) >= 1)
        return None   # angoli per tempo: ESPN non li dà
    out = []
    for cb in it["final"]["combo"]:
        res = [chk(l[2]) for l in cb["legs"]]
        ok = False if False in res else True if all(r is True for r in res) else None
        out.append({"t": cb["t"], "p": cb["p"], "est": cb["est"], "ok": ok, "legs": res})
    return out


def combo_summary(done):
    """Le MyCombo controllate: per quota obiettivo quante sono uscite contro quante il modello ne aspettava (solo le
    combo con tutte le giocate controllabili: contare quelle con una giocata incerta solo quando perdono le farebbe
    sembrare peggiori), e per tipo di giocata la probabilità media prevista contro la frequenza vera."""
    tiers, legs = {}, {}
    for it in done:
        for cb, ce in zip((it.get("final") or {}).get("combo") or [], it.get("comboEval") or []):
            if None in ce["legs"]:
                continue
            t = tiers.setdefault(str(cb["t"]), {"n": 0, "won": 0, "p": 0.0, "est": 0.0})
            t["n"] += 1
            t["won"] += ce["ok"]
            t["p"] += cb["p"]
            t["est"] += cb["est"]
            for l, r in zip(cb["legs"], ce["legs"]):
                if r is None:
                    continue
                c = l[2]
                kind = ("giocatori" if c[0] in ("pl", "ply") else "gol ed esito" if c[0] in ("esito", "tot", "mg", "gg", "sq")
                        else "cartellini" if c[0] in ("cards", "bothcards") else "angoli" if "corners" in c else "tiri di squadra")
                g = legs.setdefault(kind, {"n": 0, "p": 0.0, "hit": 0})
                g["n"] += 1
                g["p"] += l[1]
                g["hit"] += r
    if not tiers:
        return None
    return {"tiers": {k: {"n": v["n"], "won": v["won"], "exp": round(v["p"], 2), "est": round(v["est"] / v["n"], 1)}
                      for k, v in sorted(tiers.items(), key=lambda kv: float(kv[0]))},
            "legs": {k: {"n": v["n"], "p": round(v["p"] / v["n"], 3), "hit": round(v["hit"] / v["n"], 3)} for k, v in legs.items()}}


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


def market_of(x):
    """Quote del mercato salvate per una partita (server.keep_odds) -> {p1, px, p2, src}, o None."""
    od = (x or {}).get("odds")
    if not od or od.get("p1") is None:
        return None
    return {"p1": round(od["p1"], 4), "px": round(od["px"], 4), "p2": round(od["p2"], 4), "src": od.get("src"),
            **({"dec": od["dec"]} if od.get("dec") else {}), **({"ou": od["ou"]} if od.get("ou") else {})}


def evaluate_probs(f, hs, as_):
    """Esito, Brier e log loss di probabilità 1X2 qualsiasi (il pronostico o le quote del mercato)."""
    o = "1" if hs > as_ else "X" if hs == as_ else "2"
    probs = {"1": f["p1"], "X": f["px"], "2": f["p2"]}
    return {"outcome": o, "pick": max(probs, key=probs.get) == o,
            "brier": sum((probs[k] - (1 if k == o else 0)) ** 2 for k in probs),
            "ll": -math.log(max(probs[o], 1e-6))}


def evaluate(f, hs, as_):
    o = "1" if hs > as_ else "X" if hs == as_ else "2"
    probs = {"1": f["p1"], "X": f["px"], "2": f["p2"]}
    return {
        "outcome": o,
        "ll": -math.log(max(probs[o], 1e-6)),
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
    # il pronostico contro il mercato (quote dei bookmaker senza il loro margine), sulle stesse partite
    mk = [it for it in done if it.get("evalMk")]
    ll = lambda it: it["eval"].get("ll", -math.log(max(it["final"][{"1": "p1", "X": "px", "2": "p2"}[it["eval"]["outcome"]]], 1e-6)))
    market = {"n": len(mk), "brier": sum(it["eval"]["brier"] for it in mk) / len(mk),
              "brierMk": sum(it["evalMk"]["brier"] for it in mk) / len(mk),
              "ll": sum(ll(it) for it in mk) / len(mk), "llMk": sum(it["evalMk"]["ll"] for it in mk) / len(mk),
              "pick": sum(1 for it in mk if it["eval"]["pick"]) / len(mk),
              "pickMk": sum(1 for it in mk if it["evalMk"]["pick"]) / len(mk),
              "src": sorted({(it.get("market") or {}).get("src") for it in mk} - {None})} if mk else None
    return {"n": n, "pick": s("pick"), "score": s("score"), "over25": s("over25"), "btts": s("btts"),
            "brier": sum(it["eval"]["brier"] for it in done) / n, "baseBrier": base_brier, "cal": cal,
            "players": pl if pl["n"] else None, "market": market, "combo": combo_summary(done)}


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

"""Serie A Live - chicche statistiche di ogni partita.

Richiesta dell'utente del 23/10/2026: «per ogni partita una sezione dedicata alle chicche statistiche, dalle più
particolari a quelle più semplici».

Solo dati veri, nessuna stima del modello:
  - risultati delle partite (ESPN): serie aperte, bilancio in casa e fuori, partite con 3 o più gol, entrambe a segno;
  - cronaca Opta dei gol (ESPN): minuto, testa, calcio d'angolo, punizione, contropiede, da fuori area, chi è entrato
    dalla panchina, autogol, legni; da qui anche chi ha segnato il primo gol, i punti rimontati o lasciati in vantaggio
    e quelli decisi dall'85' in poi;
  - statistiche di stagione: possesso, tiri, angoli, cartellini, gol contro xG;
  - precedenti ESPN, risultati della scorsa stagione, arbitro designato (risultati delle sue partite, da server.py).
La cronaca si usa per una squadra solo se in tutte le sue partite torna con il risultato (in Süper Lig ESPN non la dà:
lì restano risultati, statistiche, precedenti e arbitro).

Quanto è particolare una chicca (r, da 0 a 1): quanto la squadra si stacca dalle altre della lega nello stesso dato (la
quante altre squadre arrivano allo stesso punto, _rare), dentro una fascia che dipende dal tipo (BAND): i minuti e il
modo dei gol, le rimonte e gli incroci tra le due squadre stanno più in alto delle serie di risultati, che stanno più
in alto dei dati semplici (bilancio in casa o fuori, precedenti, scorsa stagione, miglior marcatore). Le chicche si
mostrano dalla più particolare alla più semplice.
"""
import collections
import math

LATE = 76        # ultimo quarto d'ora: dal 76' in poi, recupero compreso
LATE_PTS = 85    # punti decisi nel finale: gol dall'85' in poi
MIN_G = 5        # gol minimi di una squadra per le quote dei suoi gol (minuti, testa, ...)
MAX_OUT = 12     # chicche per partita
MAX_TEAM = 5     # al massimo per squadra tra le particolari (le semplici a parte)
MIN_SIMPLE = 3   # chicche semplici da tenere comunque, se ci sono
# fascia di «particolarità» di ogni tipo di chicca: r = basso + (alto - basso) × distacco dalle altre squadre
BAND = {"semplice": (.1, .4), "precedenti": (.1, .6), "serie": (.3, .85), "conti": (.3, .72), "numeri": (.3, .7),
        "giocatori": (.3, .85), "arbitro": (.35, .8), "minuti": (.35, .9), "modo": (.35, .9), "punteggio": (.35, .9),
        "incrocio": (.45, .95), "ritardo": (.35, .9)}
LEVELS = ((.75, "Rara"), (.5, "Curiosa"), (0, "Semplice"))
# ritardi statistici: cose che secondo le quote delle partite giocate (1X2, senza il margine) o secondo gli xG di
# Understat sarebbero dovute succedere e non sono ancora successe in questa stagione. Si mostrano a parte, con
# l'avvertenza: provato il 23/10/2026 su 10.504 casi (cinque campionati maggiori, 2023/24-2025/26), dopo una lunga serie
# senza pareggi, vittorie o sconfitte l'evento esce come dicono le quote o un po' meno (dopo 10+ partite senza vincere
# 21,9% contro 23,8% previsto; senza perdere 15,4% contro 20,2%): il ritardo non rende l'evento più probabile.
RIT_MAX_P = .2   # si mostra un ritardo solo se una serie così capitava al massimo una volta su 5
MAX_RIT = 3      # ritardi per partita
# serie aperte: lunghezza da cui una serie è notevole di per sé (sotto, la sua rarità nella lega conta meno: _long)
LONG = {"win": 5, "unb": 7, "lose": 4, "winless": 6, "score": 7, "noscore": 4, "cs": 4, "conc": 7}
LONG_VENUE = {"win": 4, "unb": 5, "lose": 3, "winless": 4}
CATS = {"serie": "Serie aperta", "conti": "Risultati", "numeri": "Numeri di stagione", "giocatori": "Giocatori",
        "arbitro": "Arbitro", "minuti": "Minuti dei gol", "modo": "Come nascono i gol", "punteggio": "Vantaggi e rimonte",
        "incrocio": "Incrocio", "precedenti": "Precedenti", "semplice": "Da sapere", "ritardo": "Ritardo"}


# ---------- utilità ----------

def _pl(n, one, many):
    return f"{n} {one if n == 1 else many}"


def _join(parts):
    parts = [p for p in parts if p]
    return ", ".join(parts[:-1]) + " e " + parts[-1] if len(parts) > 1 else (parts[0] if parts else "")


def _rec(w, d, l, zero_l=False):
    """«5 vittorie e 2 pareggi»: le voci a zero si saltano (zero_l: «nessuna sconfitta» resta, quando è il punto)."""
    return _join([_pl(w, "vittoria", "vittorie") if w else "", _pl(d, "pareggio", "pareggi") if d else "",
                  _pl(l, "sconfitta", "sconfitte") if l else ("nessuna sconfitta" if zero_l else "")])


def _pct(x):
    return f"{round(100 * x)}%"


def _voc(k):
    """Numeri che si leggono con la vocale davanti (8, 11, 80-89, 800-899...): «degli 8», «l'80%»."""
    k = int(k)
    return k in (8, 11) or str(k)[:1] == "8" and k >= 80


def _su(k, n, sue=False):
    """«5 partite su 7» o, se sono tutte, «tutte e 7 le partite» (sue: «5 su 7», «tutte e 7 le sue», per la seconda squadra)."""
    if k == n:
        return f"tutte e {n} le {'sue' if sue else 'partite'}"
    return f"{k} su {n}" if sue else f"{k} {'partita' if k == 1 else 'partite'} su {n}"


def _dei(k):
    return f"{'degli' if _voc(k) else 'dei'} {k}"


def _il_pct(x):
    k = round(100 * x)
    return f"{'l' + chr(39) if _voc(k) else 'il '}{k}%"


def _dec(v, d=1):
    return f"{v:.{d}f}".replace(".", ",")


def _clamp(v, a=0.0, b=1.0):
    return max(a, min(b, v))


def _pts(gf, ga):
    return 3 if gf > ga else 1 if gf == ga else 0


def _band(p, t):
    """Fascia di 15 minuti di un gol, da 0 (1'-15') a 5 (76'-90' e recupero); i supplementari non contano."""
    if p == 1:
        return 0 if t <= 15 else 1 if t <= 30 else 2
    if p == 2:
        return 3 if t <= 60 else 4 if t < LATE else 5
    return None


def _rare(vals, v, high=True):
    """Quanto è raro il valore v tra quelli delle squadre della lega (vals, v compreso), da 0 a 1: 1 se nessun'altra
    squadra arriva a tanto (o scende così in basso, con high=False); poi 0,85 e giù con le squadre che arrivano allo
    stesso punto o oltre, fino a 0 quando sono un quarto della lega."""
    n = len(vals)
    if n < 2:
        return 0.0
    c = sum(1 for x in vals if (x >= v if high else x <= v))
    if c <= 1:
        return 1.0
    return .85 * max(0.0, 1 - (c - 1) / (.25 * n))


def _top(vals, v, high=True):
    """(posto, quante altre allo stesso valore): 1 = il valore più alto (o più basso, con high=False)."""
    return 1 + sum(1 for x in vals if (x > v if high else x < v)), sum(1 for x in vals if x == v) - 1


def _long(k, notable):
    return min(1.0, .5 + .5 * k / notable)


def _r(kind, ext):
    lo, hi = BAND[kind]
    return lo + (hi - lo) * _clamp(ext)


# ---------- partite delle squadre (si calcolano una volta per analisi, in model.build) ----------

def _match_goals(x, hs, as_):
    """Gol della partita dalla cronaca, in ordine di tempo: [(periodo, minuto, squadra che segna, evento)], con chi è entrato
    dalla panchina e i legni di ogni squadra. None se la cronaca manca o non torna con il risultato."""
    ev = ((x or {}).get("ev") or {}).get("ev")
    if not ev:
        return None
    goals, subs, wood = [], {"home": set(), "away": set()}, {"home": [], "away": []}
    for i, z in enumerate(ev):
        k, s = z.get("k"), z.get("s")
        if s not in ("home", "away"):
            continue
        if k == "sub" and z.get("w"):
            subs[s].add(z["w"])
        elif k == "wood":
            wood[s].append(z.get("x"))
        elif k in ("goal", "og"):
            # autogol: "s" è la squadra di chi lo fa, il gol va all'altra
            team = s if k == "goal" else ("away" if s == "home" else "home")
            goals.append((z.get("p") or 0, z.get("t") or 0, i, team, z))
    goals.sort(key=lambda g: g[:3])
    if (sum(1 for g in goals if g[3] == "home"), sum(1 for g in goals if g[3] == "away")) != (hs, as_):
        return None
    return [(p, t, team, z) for p, t, _, team, z in goals], subs, wood


def _side_view(parsed, side):
    """La partita vista da una squadra: gol fatti e subiti con minuto e tipo, punteggio all'intervallo e all'84'."""
    goals, subs, wood = parsed
    me = op = 0
    first = None
    led = trailed = False
    ht, at84 = [0, 0], [0, 0]
    gl = []
    for p, t, team, z in goals:
        mine = team == side
        if first is None:
            first = mine
        me, op = me + mine, op + (not mine)
        led, trailed = led or me > op, trailed or op > me
        if p == 1:
            ht = [me, op]
        if p == 1 or (p == 2 and t < LATE_PTS):
            at84 = [me, op]
        sit = z.get("sit")
        tags = set()
        if z.get("k") == "og":
            tags.add("og")
        else:
            if z.get("b") == "colpo di testa":
                tags.add("head")
            if sit == "corner":
                tags.add("corner")
            elif sit in ("punizione", "punizione diretta"):
                tags.add("fk")
            elif sit == "contropiede":
                tags.add("counter")
            if z.get("z") == "fuori":
                tags.add("out")
            if z.get("w") in subs[team]:
                tags.add("sub")
        gl.append({"p": p, "t": t, "b": _band(p, t), "mine": mine, "tags": sorted(tags), "who": z.get("w") if z.get("k") == "goal" else None})
    return {"goals": gl, "first": first, "led": led, "trailed": trailed, "ht": ht, "at84": at84, "wood": wood[side]}


def _p0(shots):
    """Probabilità che nessuno di questi tiri (Understat: [minuto, giocatore, xG, esito, ...]) finisse in gol."""
    out = 1.0
    for sh in shots or []:
        if sh[3] != "OwnGoal":
            out *= 1 - min(.99, max(0.0, sh[2] or 0))
    return out


def _streaks(rows):
    def run(cond):
        k = 0
        for x in reversed(rows):
            if not cond(x):
                break
            k += 1
        return k
    return {"win": run(lambda x: x["gf"] > x["ga"]), "unb": run(lambda x: x["gf"] >= x["ga"]),
            "lose": run(lambda x: x["gf"] < x["ga"]), "winless": run(lambda x: x["gf"] <= x["ga"]),
            "score": run(lambda x: x["gf"] > 0), "noscore": run(lambda x: x["gf"] == 0), "nodraw": run(lambda x: x["gf"] != x["ga"]),
            "cs": run(lambda x: x["ga"] == 0), "conc": run(lambda x: x["ga"] > 0)}


def _wdl(rows):
    return [sum(1 for x in rows if x["gf"] > x["ga"]), sum(1 for x in rows if x["gf"] == x["ga"]),
            sum(1 for x in rows if x["gf"] < x["ga"])]


def _summary(rows):
    w, d, l = _wdl(rows)
    return {"n": len(rows), "w": w, "d": d, "l": l, "gf": sum(x["gf"] for x in rows), "ga": sum(x["ga"] for x in rows),
            "pts": 3 * w + d, "st": _streaks(rows)}


def profiles(data, matches, prior=None, team_ids=None, cup=False):
    """Profilo di ogni squadra per le chicche: partite in ordine di data, serie aperte, conti della stagione, e dalla
    cronaca minuti e modo dei gol, primo gol, rimonte, finali, legni e marcatori."""
    matches = matches or {}
    played = sorted((e for e in data.get("played") or [] if e.get("hs") is not None and e.get("as") is not None),
                    key=lambda e: e.get("start") or 0)
    rows = collections.defaultdict(list)
    for e in played:
        hid, aid = str(e["home"]["id"]), str(e["away"]["id"])
        x = matches.get(str(e["id"])) or {}
        parsed = _match_goals(x, e["hs"], e["as"])
        od, us = x.get("odds") or {}, x.get("us") or {}
        for side, tid, oid, gf, ga in (("home", hid, aid, e["hs"], e["as"]), ("away", aid, hid, e["as"], e["hs"])):
            if team_ids is None or tid in team_ids:
                other = "away" if side == "home" else "home"
                rows[tid].append({"gf": gf, "ga": ga, "home": side == "home", "opp": oid, "start": e.get("start"),
                                  "v": _side_view(parsed, side) if parsed else None,
                                  # quote senza il margine (vittoria, pareggio, sconfitta della squadra) e xG Understat
                                  "odds": ((od["p1"], od["px"], od["p2"]) if side == "home" else (od["p2"], od["px"], od["p1"]))
                                  if all(isinstance(od.get(k), (int, float)) for k in ("p1", "px", "p2")) else None,
                                  "xg": (sum(sh[2] for sh in us.get(side) or []), sum(sh[2] for sh in us.get(other) or []))
                                  if us else None,
                                  # probabilità di nessun gol, fatto e subito, tiro per tiro dagli xG (autogol esclusi)
                                  "p0": (_p0(us.get(side)), _p0(us.get(other))) if us else None})
    prev = collections.defaultdict(list)
    if not cup:
        for e in sorted((e for e in (prior or {}).get("results") or [] if e.get("hs") is not None and e.get("as") is not None),
                        key=lambda e: e.get("start") or 0):
            prev[str(e["home"]["id"])].append(_pts(e["hs"], e["as"]))
            prev[str(e["away"]["id"])].append(_pts(e["as"], e["hs"]))
    out = {}
    for tid, rs in rows.items():
        p = _summary(rs)
        p["venue"] = {"home": _summary([x for x in rs if x["home"]]), "away": _summary([x for x in rs if not x["home"]])}
        p["o25"] = sum(1 for x in rs if x["gf"] + x["ga"] >= 3)
        p["btts"] = sum(1 for x in rs if x["gf"] and x["ga"])
        p["cs"] = sum(1 for x in rs if x["ga"] == 0)
        p["fts"] = sum(1 for x in rs if x["gf"] == 0)
        pv = prev.get(tid) or []
        p["prevPts"] = sum(pv[:len(rs)]) if len(pv) >= len(rs) else None
        p["ev"] = _ev_profile(rs) if all(x["v"] for x in rs) else None
        p["_rows"] = rs
        p["_s"] = ((data.get("teams") or {}).get(tid) or {}).get("stats")
        out[tid] = p
    return out


def index(data, matches, prior=None, team_ids=None, cup=False):
    """Quello che serve alle chicche, calcolato una volta per analisi (model.build): profili delle squadre e risultati
    della scorsa stagione (per i precedenti diretti)."""
    prev = [(str(e["home"]["id"]), str(e["away"]["id"]), e["hs"], e["as"], e.get("start") or 0)
            for e in (prior or {}).get("results") or [] if e.get("hs") is not None and e.get("as") is not None]
    played = [e for e in data.get("played") or [] if e.get("hs") is not None]
    us_share = sum(1 for e in played if ((matches or {}).get(str(e["id"])) or {}).get("us")) / len(played) if played else 0
    return {"P": profiles(data, matches, prior, team_ids, cup), "prev": prev, "us": us_share >= .9 and not cup}


def _ev_profile(rs):
    bf, ba = [0] * 6, [0] * 6
    tf, ta = collections.Counter(), collections.Counter()
    first_for, first_ag = [], []
    cb = dr = late_g = late_l = 0
    wood = []
    scorers = collections.Counter()
    per_match = []
    for x in rs:
        v = x["v"]
        names = set()
        for g in v["goals"]:
            if g["b"] is not None:
                (bf if g["mine"] else ba)[g["b"]] += 1
            (tf if g["mine"] else ta).update(g["tags"])
            if g["mine"] and g["who"]:
                scorers[g["who"]] += 1
                names.add(g["who"])
        per_match.append(names)
        if v["first"] is True:
            first_for.append(x)
        elif v["first"] is False:
            first_ag.append(x)
        pts = _pts(x["gf"], x["ga"])
        if v["trailed"]:
            cb += pts
        if v["led"]:
            dr += 3 - pts
        d84 = pts - _pts(*v["at84"])
        late_g, late_l = late_g + max(0, d84), late_l + max(0, -d84)
        wood += v["wood"]
    streak = {}
    for name in per_match[-1] if per_match else ():
        k = 0
        for names in reversed(per_match):
            if name not in names:
                break
            k += 1
        streak[name] = k
    return {"bf": bf, "ba": ba, "h1f": sum(bf[:3]), "h1a": sum(ba[:3]), "tf": dict(tf), "ta": dict(ta),
            "firstFor": _wdl(first_for), "firstAg": _wdl(first_ag), "cb": cb, "cbN": sum(1 for x in rs if x["v"]["trailed"]),
            "drop": dr, "ldN": sum(1 for x in rs if x["v"]["led"]), "lateG": late_g, "lateL": late_l,
            "wood": len(wood), "pali": sum(1 for w in wood if w == "palo"), "trav": sum(1 for w in wood if w == "traversa"),
            "scorers": scorers.most_common(), "nScorers": len(scorers), "streak": streak}


# ---------- chicche di una partita ----------

class _Out:
    def __init__(self):
        self.items = []

    def add(self, kind, ext, text, team=None, grp=None, key=None, r=None):
        self.items.append({"t": text, "team": team, "cat": CATS[kind], "kind": kind,
                           "r": round(_clamp(_r(kind, ext) if r is None else r), 3), "grp": grp, "key": key})


def _where(league):
    return f"in {league}"


def _most(vals, v, league, high=True):
    """Frase sul primato: «, più di qualsiasi altra squadra in Serie A»; senza primato, la media della lega per confronto."""
    k, ties = _top(vals, v, high)
    if k != 1:
        avg = sum(vals) / len(vals) if vals else 0
        return f". I{_where(league)[1:]} la media è {_dec(avg)} a squadra"
    if not ties:
        return f", {'più' if high else 'meno'} di qualsiasi altra squadra {_where(league)}"
    return f", il numero più {'alto' if high else 'basso'} {_where(league)} insieme " + (
        "a un'altra squadra" if ties == 1 else f"ad altre {ties} squadre")


def _team_facts(o, PP, tid, venue, X, league, cup, players):
    p = PP[tid]
    n = p["n"]
    min_n = 3 if cup else 4
    teams = list(PP.values())
    vals = lambda f, need=lambda q: True: [f(q) for q in teams if need(q)]
    st = p["st"]

    # serie aperte (una sola per tipo: risultati, gol fatti, gol subiti)
    def s_vals(k):
        return vals(lambda q: q["st"][k])
    rec_last = lambda k: _rec(*_wdl_last(p, k))
    if st["win"] >= 3:
        uniq = st["win"] == n and n >= min_n and sum(1 for q in teams if q["n"] and q["w"] == q["n"]) == 1
        t = f"{X} ha vinto tutte e {n} le partite giocate finora." if st["win"] == n else f"{X} vince da {st['win']} partite di fila."
        o.add("serie", _rare(s_vals("win"), st["win"]) * _long(st["win"], LONG["win"]), t + (f" È l'unica squadra {_where(league)} a punteggio pieno." if uniq else ""),
              tid, f"ris:{tid}", f"win:{tid}")
    if st["unb"] >= 4 and st["unb"] > st["win"]:
        k = st["unb"]
        uniq = k == n and sum(1 for q in teams if q["l"] == 0) == 1
        t = (f"{X} non ha ancora perso in questa stagione: {rec_last(k)}." if k == n else f"{X} non perde da {k} partite: {rec_last(k)}.")
        o.add("serie", _rare(s_vals("unb"), k) * _long(k, LONG["unb"]), t + (f" È l'unica squadra {_where(league)} ancora imbattuta." if uniq else ""),
              tid, f"ris:{tid}", f"unb:{tid}")
    if st["lose"] >= 3:
        k = st["lose"]
        t = f"{X} ha perso tutte e {n} le partite giocate finora." if k == n else f"{X} ha perso le ultime {k} partite."
        o.add("serie", _rare(s_vals("lose"), k) * _long(k, LONG["lose"]), t, tid, f"ris:{tid}", f"lose:{tid}")
    if st["winless"] >= 4 and st["winless"] > st["lose"]:
        k = st["winless"]
        uniq = k == n and sum(1 for q in teams if q["w"] == 0) == 1
        t = (f"{X} non ha ancora vinto in questa stagione: {rec_last(k)}." if k == n else f"{X} non vince da {k} partite: {rec_last(k)}.")
        o.add("serie", _rare(s_vals("winless"), k) * _long(k, LONG["winless"]), t + (f" È l'unica squadra {_where(league)} ancora senza vittorie." if uniq else ""),
              tid, f"ris:{tid}", f"winless:{tid}")
    if st["score"] >= 5 or (st["score"] == n and n >= min_n):
        k = st["score"]
        t = f"{X} ha segnato in tutte e {n} le partite giocate finora." if k == n else f"{X} segna da {k} partite di fila."
        o.add("serie", _rare(s_vals("score"), k) * _long(k, LONG["score"]), t, tid, f"gf:{tid}", f"score:{tid}")
    if st["noscore"] >= 2:
        k = st["noscore"]
        t = f"{X} non ha ancora segnato in questa stagione." if k == n else f"{X} non segna da {k} partite."
        o.add("serie", _rare(s_vals("noscore"), k) * _long(k, LONG["noscore"]), t, tid, f"gf:{tid}", f"noscore:{tid}")
    if st["cs"] >= 3:
        k = st["cs"]
        t = f"{X} non ha ancora subito gol in questa stagione." if k == n else f"{X} non subisce gol da {k} partite di fila."
        o.add("serie", _rare(s_vals("cs"), k) * _long(k, LONG["cs"]), t, tid, f"ga:{tid}", f"cs:{tid}")
    if st["conc"] >= 6 or (st["conc"] == n and n >= 5):
        k = st["conc"]
        t = (f"{X} ha subito almeno un gol in tutte e {n} le partite giocate finora." if k == n
             else f"{X} subisce almeno un gol da {k} partite di fila.")
        o.add("serie", _rare(s_vals("conc"), k) * _long(k, LONG["conc"]), t, tid, f"ga:{tid}", f"conc:{tid}")

    # in casa o in trasferta (dove si gioca questa partita)
    where = "in casa" if venue == "home" else "in trasferta"
    V = p["venue"][venue]
    vn, vs = V["n"], V["st"]
    v_vals = lambda k: vals(lambda q: q["venue"][venue]["st"][k])
    if vn:
        if vs["win"] >= 3:
            t = f"{X} {where} ha vinto tutte e {vn} le partite." if vs["win"] == vn else f"{X} {where} vince da {vs['win']} partite di fila."
            o.add("serie", _rare(v_vals("win"), vs["win"]) * _long(vs["win"], LONG_VENUE["win"]), t, tid, f"ven:{tid}")
        elif vs["unb"] >= 4:
            k = vs["unb"]
            t = (f"{X} {where} non ha ancora perso: {_rec(*_wdl_last(p, k, venue))}." if k == vn
                 else f"{X} {where} non perde da {k} partite: {_rec(*_wdl_last(p, k, venue))}.")
            o.add("serie", _rare(v_vals("unb"), k) * _long(k, LONG_VENUE["unb"]), t, tid, f"ven:{tid}")
        if vs["lose"] >= 3:
            t = f"{X} {where} ha perso tutte e {vn} le partite." if vs["lose"] == vn else f"{X} {where} ha perso le ultime {vs['lose']} partite."
            o.add("serie", _rare(v_vals("lose"), vs["lose"]) * _long(vs["lose"], LONG_VENUE["lose"]), t, tid, f"ven:{tid}")
        elif vs["winless"] >= 3:
            k = vs["winless"]
            t = (f"{X} {where} non ha ancora vinto: {_rec(*_wdl_last(p, k, venue))}." if k == vn
                 else f"{X} {where} non vince da {k} partite: {_rec(*_wdl_last(p, k, venue))}.")
            o.add("serie", _rare(v_vals("winless"), k) * _long(k, LONG_VENUE["winless"]), t, tid, f"ven:{tid}")
        # bilancio semplice in casa o fuori
        ppg = V["pts"] / vn
        o.add("semplice", _rare(vals(lambda q: q["venue"][venue]["pts"] / q["venue"][venue]["n"], lambda q: q["venue"][venue]["n"]), ppg),
              f"{X} {where}: {_rec(V['w'], V['d'], V['l'])}, con {_pl(V['gf'], 'gol fatto', 'gol fatti') if V['gf'] else 'nessun gol fatto'} e "
              f"{_pl(V['ga'], 'subito', 'subiti') if V['ga'] else 'nessuno subito'}.",
              tid, f"bil:{tid}")

    elig = lambda q: q["n"] >= min_n
    if n >= min_n:
        # conti della stagione
        sh = p["o25"] / n
        o_vals = vals(lambda q: q["o25"] / q["n"], elig)
        if sh >= .7:
            o.add("conti", _rare(o_vals, sh), f"{X}: almeno 3 gol in {_su(p['o25'], n)}.", tid, None, f"o25:{tid}")
        elif sh <= .2:
            t = (f"{X}: mai più di 2 gol nelle {n} partite giocate." if not p["o25"]
                 else f"{X}: più di 2 gol solo in {_su(p['o25'], n)}.")
            o.add("conti", _rare(o_vals, sh, False), t, tid, None, f"u25:{tid}")
        sh = p["btts"] / n
        b_vals = vals(lambda q: q["btts"] / q["n"], elig)
        if sh >= .7:
            o.add("conti", _rare(b_vals, sh), f"{X}: entrambe le squadre a segno in {_su(p['btts'], n)}.", tid, None, f"btts:{tid}")
        elif sh <= .2:
            t = (f"{X}: mai entrambe le squadre a segno nelle {n} partite giocate." if not p["btts"]
                 else f"{X}: entrambe le squadre a segno solo in {_su(p['btts'], n)}.")
            o.add("conti", _rare(b_vals, sh, False), t, tid, None, f"nobtts:{tid}")
        if p["d"] == 0 and n >= 5:
            only = sum(1 for q in teams if elig(q) and q["d"] == 0) == 1
            o.add("conti", _rare(vals(lambda q: q["d"] / q["n"], elig), 0, False),
                  f"{X} non ha ancora pareggiato: {_rec(p['w'], 0, p['l'])} in {n} partite."
                  + (f" È l'unica squadra {_where(league)} senza pareggi." if only else ""), tid, None, f"nod:{tid}")
        elif p["d"] >= max(4, n / 2):
            o.add("conti", _rare(vals(lambda q: q["d"] / q["n"], elig), p["d"] / n),
                  f"{X} ha pareggiato {p['d']} delle {n} partite giocate.", tid, None, f"d:{tid}")
        cs_vals = vals(lambda q: q["cs"], elig)
        if p["cs"] >= 3 and _top(cs_vals, p["cs"])[0] <= 2 and st["cs"] < 3:
            o.add("conti", _rare(cs_vals, p["cs"]), f"{X} ha chiuso {p['cs']} delle {n} partite senza subire gol"
                  + _most(cs_vals, p["cs"], league) + ".", tid, f"ga:{tid}", f"csn:{tid}")
        f_vals = vals(lambda q: q["fts"], elig)
        if p["fts"] >= 3 and _top(f_vals, p["fts"])[0] <= 2 and st["noscore"] < 2:
            o.add("conti", _rare(f_vals, p["fts"]), f"{X} non ha segnato in {p['fts']} delle {n} partite"
                  + (f": nessuna squadra {_where(league)} è rimasta a secco più volte" if _top(f_vals, p["fts"]) == (1, 0) else "") + ".",
                  tid, f"gf:{tid}", f"fts:{tid}")

        # dalla cronaca
        E = p["ev"]
        if E:
            evq = [q for q in teams if q["ev"] and elig(q)]
            _ev_facts(o, p, E, evq, tid, X, league)

        # numeri di stagione dai tabellini e da Understat/Opta
        _num_facts(o, PP, tid, X, league, elig)

    # stagione scorsa allo stesso punto
    if p.get("prevPts") is not None and n >= 3:
        d = p["pts"] - p["prevPts"]
        dv = vals(lambda q: abs(q["pts"] - q["prevPts"]), lambda q: q.get("prevPts") is not None)
        t = (f"{X} ha {_pl(p['pts'], 'punto', 'punti')} dopo {n} partite: "
             + (f"{_pl(abs(d), 'punto', 'punti')} {'in più' if d > 0 else 'in meno'} delle prime {n} della scorsa stagione ({p['prevPts']})."
                if d else f"gli stessi delle prime {n} della scorsa stagione."))
        o.add("semplice" if abs(d) < 5 else "conti", _rare(dv, abs(d)), t, tid, f"prev:{tid}")

    # giocatori
    E = p["ev"]
    if E and E["streak"]:
        name, k = max(E["streak"].items(), key=lambda kv: kv[1])
        if k >= 3:
            t = (f"{name} ha segnato in tutte e {n} le partite della sua squadra." if k == n
                 else f"{name} ha segnato in ciascuna delle ultime {k} partite della sua squadra.")
            o.add("giocatori", {3: .5, 4: .75}.get(k, 1.0), t, tid, f"bomber:{tid}")
    gf = p["gf"]
    if E and E["scorers"] and gf >= MIN_G:
        name, g = E["scorers"][0]
        sh = g / gf
        tops = [q["ev"]["scorers"][0][1] / q["gf"] for q in teams if q["ev"] and q["ev"]["scorers"] and q["gf"] >= MIN_G]
        if sh >= .4 and (len(E["scorers"]) < 2 or E["scorers"][1][1] < g):
            o.add("giocatori", _rare(tops, sh), f"{name} ha segnato {g} {_dei(gf)} gol della sua squadra ({_pct(sh)}).", tid, f"bomber:{tid}")
    if E and n >= min_n:
        sv = [q["ev"]["nScorers"] for q in teams if q["ev"] and elig(q)]
        k, ties = _top(sv, E["nScorers"])
        if k == 1 and E["nScorers"] >= 6:
            o.add("giocatori", _rare(sv, E["nScorers"]), f"{X} ha già mandato in gol {E['nScorers']} giocatori diversi"
                  + _most(sv, E["nScorers"], league) + ".", tid, None, f"nsc:{tid}")
    mine = [q for q in players if str(q.get("teamId")) == tid and int(q.get("goals") or 0) > 0]
    g = max((int(q.get("goals") or 0) for q in mine), default=0)
    best = sorted((q for q in mine if int(q.get("goals") or 0) == g), key=lambda q: -(q.get("assists") or 0))
    if len(best) == 1:
        a = int(best[0].get("assists") or 0)
        o.add("semplice", .3, f"{X}: il miglior marcatore è {best[0].get('name')}, con {_pl(g, 'gol', 'gol')}"
              + (f" e {_pl(a, 'assist', 'assist')}" if a else "") + ".", tid, f"bomber:{tid}")
    elif 1 < len(best) <= 3:
        o.add("semplice", .3, f"{X}: i migliori marcatori sono {_join([q.get('name') for q in best])}, con {_pl(g, 'gol', 'gol')} a testa.",
              tid, f"bomber:{tid}")
    elif best:
        o.add("semplice", .6, f"{X} non ha un vero bomber: {len(best)} giocatori con {_pl(g, 'gol', 'gol')}, nessuno di più.", tid, f"bomber:{tid}")


def _wdl_last(p, k, venue=None):
    """Vittorie, pareggi e sconfitte delle ultime k partite (in casa o fuori, se venue)."""
    rs = p["_rows"] if venue is None else [x for x in p["_rows"] if x["home"] == (venue == "home")]
    return _wdl(rs[-k:])


def _ev_facts(o, p, E, evq, tid, X, league):
    gf, ga = p["gf"], p["ga"]
    ok_f = [q for q in evq if q["gf"] >= MIN_G]
    ok_a = [q for q in evq if q["ga"] >= MIN_G]
    lg_f = sum(q["ev"]["bf"][5] for q in evq) / max(1, sum(sum(q["ev"]["bf"]) for q in evq))

    # minuti dei gol
    if gf >= MIN_G:
        sh = E["bf"][5] / gf
        vs = [q["ev"]["bf"][5] / q["gf"] for q in ok_f]
        if sh >= .35 and _rare(vs, sh) >= .3:
            o.add("minuti", _rare(vs, sh), f"{X} ha segnato {E['bf'][5]} dei suoi {gf} gol dal 76' in poi ({_pct(sh)}): "
                  f"{_where(league)} la media è {_pct(lg_f)}.", tid, None, f"latef:{tid}")
        h1 = E["h1f"] / gf
        vs = [q["ev"]["h1f"] / q["gf"] for q in ok_f]
        if E["h1f"] == 0:
            o.add("minuti", _rare(vs, h1, False), f"{X} non ha ancora segnato nel primo tempo: tutti e {gf} i gol sono arrivati nella ripresa.",
                  tid, f"h1f:{tid}")
        elif h1 <= .25 and _rare(vs, h1, False) >= .3:
            o.add("minuti", _rare(vs, h1, False), f"{X} segna soprattutto nella ripresa: {gf - E['h1f']} {_dei(gf)} gol sono arrivati nel secondo tempo.",
                  tid, f"h1f:{tid}")
        elif h1 >= .65 and _rare(vs, h1) >= .3:
            o.add("minuti", _rare(vs, h1), f"{X} segna soprattutto nel primo tempo: {E['h1f']} {_dei(gf)} gol.", tid, f"h1f:{tid}")
    if ga >= MIN_G:
        lg_a = lg_f   # nella lega i gol subiti sono gli stessi segnati
        sh = E["ba"][5] / ga
        vs = [q["ev"]["ba"][5] / q["ga"] for q in ok_a]
        if sh >= .35 and _rare(vs, sh) >= .3:
            o.add("minuti", _rare(vs, sh), f"{X} ha subito {E['ba'][5]} {_dei(ga)} gol dal 76' in poi ({_pct(sh)}): "
                  f"{_where(league)} la media è {_pct(lg_a)}.", tid, None, f"latea:{tid}")
    if ga >= 4:
        vs = [q["ev"]["h1a"] / q["ga"] for q in evq if q["ga"] >= 4]
        h1 = E["h1a"] / ga
        if E["h1a"] == 0:
            o.add("minuti", _rare(vs, h1, False), f"{X} non ha ancora subito gol nel primo tempo: tutti e {ga} i gol subiti sono arrivati nella ripresa.",
                  tid, f"h1a:{tid}")
        elif h1 >= .7 and _rare(vs, h1) >= .3:
            o.add("minuti", _rare(vs, h1), f"{X} subisce soprattutto nel primo tempo: {E['h1a']} {_dei(ga)} gol.", tid, f"h1a:{tid}")
    for key, side, txt in (("bf", "f", "segnato"), ("ba", "a", "subito")):
        k = E[key][0]
        vs = [q["ev"][key][0] for q in evq]
        if k >= 3 and _top(vs, k)[0] == 1:
            o.add("minuti", _rare(vs, k), f"{X} ha {txt} {k} gol nei primi 15 minuti" + _most(vs, k, league) + ".",
                  tid, None, f"early{side}:{tid}")

    # primo gol, rimonte, vantaggi persi, finali
    w, d, l = E["firstFor"]
    k = w + d + l
    if k >= 3:
        vs = [(3 * q["ev"]["firstFor"][0] + q["ev"]["firstFor"][1]) / (3 * sum(q["ev"]["firstFor"])) for q in evq if sum(q["ev"]["firstFor"]) >= 3]
        share = (3 * w + d) / (3 * k)
        if w == k:
            o.add("punteggio", _rare(vs, share), f"Nelle {k} partite in cui ha segnato il primo gol, {X} ha sempre vinto.", tid, f"lead:{tid}")
        elif l == 0:
            o.add("punteggio", _rare(vs, share) * .8, f"Nelle {k} partite in cui ha segnato il primo gol, {X} non ha mai perso: {_rec(w, d, 0)}.", tid, f"lead:{tid}")
        elif l >= 2 and _rare(vs, share, False) >= .3:
            o.add("punteggio", _rare(vs, share, False), f"{X} ha perso {l} delle {k} partite in cui aveva segnato il primo gol.", tid, f"lead:{tid}")
    w, d, l = E["firstAg"]
    k = w + d + l
    if k >= 3:
        vs = [(3 * q["ev"]["firstAg"][0] + q["ev"]["firstAg"][1]) / (3 * sum(q["ev"]["firstAg"])) for q in evq if sum(q["ev"]["firstAg"]) >= 3]
        share = (3 * w + d) / (3 * k)
        if w + d == 0:
            o.add("punteggio", _rare(vs, share, False) * .9, f"Nelle {k} partite in cui ha subito il primo gol, {X} ha sempre perso.", tid, f"comeback:{tid}")
        elif share >= .4 and _rare(vs, share) >= .3:
            o.add("punteggio", _rare(vs, share), f"Nelle {k} partite in cui ha subito il primo gol, {X} ha fatto {_pl(3 * w + d, 'punto', 'punti')}: "
                  f"{_rec(w, d, l)}.", tid, f"comeback:{tid}")
    vs = [q["ev"]["cb"] for q in evq]
    if E["cb"] >= 4 and _top(vs, E["cb"])[0] == 1:
        o.add("punteggio", _rare(vs, E["cb"]), f"{X} ha conquistato {E['cb']} punti in partite in cui era in svantaggio"
              + _most(vs, E["cb"], league) + ".", tid, f"comeback:{tid}")
    vs = [q["ev"]["drop"] for q in evq]
    if E["drop"] >= 4 and _rare(vs, E["drop"]) >= .3:
        o.add("punteggio", _rare(vs, E["drop"]), f"{X} ha lasciato {E['drop']} punti in partite in cui era in vantaggio"
              + _most(vs, E["drop"], league) + ".", tid, f"lead:{tid}")
    vs = [q["ev"]["lateG"] for q in evq]
    if E["lateG"] >= 3 and _rare(vs, E["lateG"]) >= .3:
        o.add("punteggio", _rare(vs, E["lateG"]), f"{X} ha guadagnato {E['lateG']} punti con gol dall'85' in poi"
              + _most(vs, E["lateG"], league) + ".", tid, f"late:{tid}")
    vs = [q["ev"]["lateL"] for q in evq]
    if E["lateL"] >= 3 and _rare(vs, E["lateL"]) >= .3:
        o.add("punteggio", _rare(vs, E["lateL"]), f"{X} ha perso {E['lateL']} punti per gol subiti dall'85' in poi"
              + _most(vs, E["lateL"], league) + ".", tid, f"late:{tid}")

    # come nascono i gol, fatti e subiti
    kinds = (("head", "di testa"), ("corner", "nati da calcio d'angolo"), ("fk", "nati da calcio di punizione"),
             ("counter", "in contropiede"), ("out", "da fuori area"), ("sub", "con giocatori entrati dalla panchina"))
    for tag, what in kinds:
        k = E["tf"].get(tag, 0)
        vs = [q["ev"]["tf"].get(tag, 0) for q in evq]
        if k >= (2 if tag == "fk" else 3) and _rare(vs, k) >= .3:
            text = f"{X} ha segnato di testa {k} dei suoi {gf} gol" if tag == "head" else f"{X} ha segnato {k} gol {what}"
            o.add("modo", _rare(vs, k), text + _most(vs, k, league) + ".",
                  tid, None, f"tf{tag}:{tid}")
    for tag, what in kinds[:5]:
        k = E["ta"].get(tag, 0)
        vs = [q["ev"]["ta"].get(tag, 0) for q in evq]
        if k >= (2 if tag == "fk" else 3) and _rare(vs, k) >= .3:
            o.add("modo", _rare(vs, k), f"{X} ha subito {k} gol {what}" + _most(vs, k, league) + ".",
                  tid, None, f"ta{tag}:{tid}")
    k = E["tf"].get("og", 0)
    vs = [q["ev"]["tf"].get("og", 0) for q in evq]
    if k >= 2 and _top(vs, k)[0] == 1:
        o.add("modo", _rare(vs, k), f"{X} ha già avuto {k} autogol a favore" + _most(vs, k, league) + ".", tid, None, f"ogf:{tid}")
    k = E["ta"].get("og", 0)
    vs = [q["ev"]["ta"].get("og", 0) for q in evq]
    if k >= 2 and _top(vs, k)[0] == 1:
        o.add("modo", _rare(vs, k), f"{X} ha già fatto {k} autogol" + _most(vs, k, league) + ".", tid, None, f"oga:{tid}")
    vs = [q["ev"]["wood"] for q in evq]
    if E["wood"] >= 4 and _rare(vs, E["wood"]) >= .3:
        parts = _join([_pl(E["pali"], "palo", "pali") if E["pali"] else "", _pl(E["trav"], "traversa", "traverse") if E["trav"] else ""])
        o.add("modo", _rare(vs, E["wood"]), f"{X} ha colpito {E['wood']} legni ({parts})" + _most(vs, E["wood"], league) + ".",
              tid, None, f"wood:{tid}")


NUM_KEYS = (("averageBallPossession", False, 0, "{X} ha il possesso palla medio più alto {w}: {v}%.", "{X} ha il possesso palla medio più basso {w}: {v}%."),
            ("shots", True, 1, "{X} è la squadra che tira di più {w}: {v} tiri a partita.", "{X} è la squadra che tira di meno {w}: {v} tiri a partita."),
            ("corners", True, 1, "{X} è la squadra che batte più calci d'angolo {w}: {v} a partita.",
             "{X} è la squadra che batte meno calci d'angolo {w}: {v} a partita."),
            ("yellowCards", True, 1, "{X} è la squadra più ammonita {w}: {v} gialli a partita.", "{X} è la squadra meno ammonita {w}: {v} gialli a partita."))


def _num_facts(o, PP, tid, X, league, elig):
    """Primati della lega nelle statistiche di stagione (solo il primo posto da sola, in alto o in basso)."""
    S = {t: q["_s"] for t, q in PP.items() if q.get("_s") and elig(q)}
    s = S.get(tid)
    if not s or len(S) < 4:
        return
    where = _where(league)
    isnum = lambda v: isinstance(v, (int, float)) and not isinstance(v, bool)
    for key, per_game, dec, hi_t, lo_t in NUM_KEYS:
        get = lambda x: (x[key] / x["matches"] if per_game else x[key]) if isnum(x.get(key)) and x.get("matches") else None
        vs = [v for v in (get(x) for x in S.values()) if v is not None]
        v = get(s)
        if v is None or len(vs) < 4:
            continue
        for high, tmpl in ((True, hi_t), (False, lo_t)):
            if _top(vs, v, high) == (1, 0):
                o.add("numeri", _rare(vs, v, high), tmpl.format(X=X, w=where, v=_dec(v, dec)), tid, None, f"{key}:{tid}")
    r = s.get("redCards")
    vs = [x.get("redCards") or 0 for x in S.values()]
    if isnum(r) and r >= 3 and _top(vs, r)[0] == 1:
        o.add("numeri", _rare(vs, r), f"{X} ha già avuto {int(r)} espulsioni" + _most(vs, r, league) + ".", tid, None, f"red:{tid}")
    # gol contro xG (stesse partite: Understat, o ESPN dove manca)
    xg = {t: x for t, x in S.items() if isinstance(x.get("expectedGoals"), (int, float)) and isinstance(x.get("expectedGoalsAgainst"), (int, float))
          and (x.get("usMatches") in (None, x.get("matches")))}
    if tid in xg and len(xg) >= 4:
        diff = {t: (x.get("goalsScored") or 0) - x["expectedGoals"] for t, x in xg.items()}
        d = diff[tid]
        vs = list(diff.values())
        x = xg[tid]
        if d >= 3 and _top(vs, d) == (1, 0):
            o.add("numeri", _rare(vs, d), f"{X} ha segnato {int(x.get('goalsScored') or 0)} gol con {_dec(x['expectedGoals'])} xG: "
                  f"{_dec(d)} in più, lo scarto più alto {where}.", tid, None, f"xg:{tid}")
        elif d <= -3 and _top(vs, d, False) == (1, 0):
            o.add("numeri", _rare(vs, d, False), f"{X} ha segnato {int(x.get('goalsScored') or 0)} gol con {_dec(x['expectedGoals'])} xG: "
                  f"{_dec(-d)} in meno, lo scarto più ampio {where}.", tid, None, f"xg:{tid}")
        diff = {t: x["expectedGoalsAgainst"] - (x.get("goalsConceded") or 0) for t, x in xg.items()}
        d = diff[tid]
        vs = list(diff.values())
        if d >= 3 and _top(vs, d) == (1, 0):
            o.add("numeri", _rare(vs, d), f"{X} ha subito {int(x.get('goalsConceded') or 0)} gol a fronte di {_dec(x['expectedGoalsAgainst'])} "
                  f"xG concessi: {_dec(d)} in meno del previsto, il dato migliore {where}.", tid, None, f"xga:{tid}")
        elif d <= -3 and _top(vs, d, False) == (1, 0):
            o.add("numeri", _rare(vs, d, False), f"{X} ha subito {int(x.get('goalsConceded') or 0)} gol a fronte di {_dec(x['expectedGoalsAgainst'])} "
                  f"xG concessi: {_dec(-d)} in più del previsto, il dato peggiore {where}.", tid, None, f"xga:{tid}")


# ---------- ritardi statistici ----------

def _once(P):
    return f"circa una volta su {max(2, round(1 / P))}"


def _drought(rows, prob):
    """(probabilità che in queste partite l'evento non capitasse mai, volte in cui era atteso); None se manca un dato."""
    ps = [prob(x) for x in rows]
    if not ps or any(q is None for q in ps):
        return None
    P = 1.0
    for q in ps:
        P *= 1 - q
    return P, sum(ps)


def _rit_r(P):
    """Particolarità di un ritardo dalla sua probabilità: una volta su 10 = 0,5, una su 100 o meno = 1."""
    return _clamp(math.log10(1 / max(P, 1e-9)) / 2)


def _ritardi(o, p, tid, X, players, us):
    """Ritardi di una squadra e del suo giocatore più in ritardo sugli xG; ogni ritardo prende il posto della serie che
    racconta la stessa cosa ("rep"), se viene mostrato."""
    rs, n, st = p["_rows"], p["n"], p["st"]
    odds = lambda i: lambda x: x["odds"][i] if x["odds"] else None
    for key, k, i, base_all, base_k, verb in (
            ("winless", st["winless"], 0, "non ha ancora vinto in questa stagione", "non vince da {k} partite", "vinte"),
            ("nodraw", st["nodraw"], 1, "non ha ancora pareggiato in questa stagione", "non pareggia da {k} partite", "pareggiate"),
            ("unb", st["unb"], 2, "non ha ancora perso in questa stagione", "non perde da {k} partite", "perse")):
        D = _drought(rs[-k:], odds(i)) if k >= 4 else None
        if D and 0 < D[0] <= RIT_MAX_P and D[1] >= 1:
            o.add("ritardo", _rit_r(D[0]), f"{X} {base_all if k == n else base_k.format(k=k)}: secondo le quote ne avrebbe {verb} "
                  f"circa {_dec(D[1])}. Una serie così capitava {_once(D[0])}.", tid, f"rit:{key}:{tid}")
            o.items[-1]["rep"] = [f"nod:{tid}"] if key == "nodraw" else [f"{key}:{tid}"]
    k = st["noscore"]
    D = _drought(rs[-k:], lambda x: 1 - x["p0"][0] if x["p0"] else None) if k >= 2 else None
    if D and 0 < D[0] <= (RIT_MAX_P if k >= 3 else RIT_MAX_P / 2):
        xg = sum(x["xg"][0] for x in rs[-k:])
        o.add("ritardo", _rit_r(D[0]), f"{X} non segna da {k} partite pur avendo creato {_dec(xg)} xG: restare a secco con quelle "
              f"occasioni capitava {_once(D[0])}.", tid, f"rit:noscore:{tid}")
        o.items[-1]["rep"] = [f"noscore:{tid}"]
    k = st["conc"]
    # gol subiti veri (non solo autogol) in ogni partita della serie, se no gli xG degli avversari non la spiegano
    real = all(x["v"] and any(not g["mine"] and "og" not in g["tags"] for g in x["v"]["goals"]) for x in rs[-k:]) if k else False
    D = _drought(rs[-k:], lambda x: x["p0"][1] if x["p0"] else None) if k >= 4 and real else None
    if D and 0 < D[0] <= RIT_MAX_P:
        xga = sum(x["xg"][1] for x in rs[-k:])
        o.add("ritardo", _rit_r(D[0]), f"{X} subisce almeno un gol da {k} partite di fila, anche se gli avversari hanno creato solo "
              f"{_dec(xga)} xG: senza mai una porta inviolata capitava {_once(D[0])}.", tid, f"rit:conc:{tid}")
        o.items[-1]["rep"] = [f"conc:{tid}"]
    if not us:
        return
    # giocatori: gol su azione molto sotto gli xG senza rigori (Understat, con minuti e gol che tornano con ESPN)
    best = None
    for q in players:
        if str(q.get("teamId")) != tid:
            continue
        lam, g, mins = q.get("npxG"), q.get("npg"), q.get("minutesPlayed") or 0
        if not isinstance(lam, (int, float)) or not isinstance(g, (int, float)) or lam < 2 or mins < 270:
            continue
        if q.get("minutesEspn") is not None and abs(mins - q["minutesEspn"]) > 45 or g > (q.get("goalsEspn") or 0):
            continue
        g = int(g)
        P = sum(math.exp(-lam) * lam ** j / math.factorial(j) for j in range(g + 1))
        if lam - g >= 1.5 and P <= .1 and (best is None or P < best[0]):
            best = (P, q, lam, g)
    if best:
        P, q, lam, g = best
        o.add("ritardo", _rit_r(P), (f"{q.get('name')} non ha ancora segnato su azione pur avendo {_dec(lam)} xG: con quelle occasioni "
                                     f"restare a zero capitava {_once(P)}." if not g else
                                     f"{q.get('name')} ha segnato solo {_pl(g, 'gol', 'gol')} su azione con {_dec(lam)} xG: con quelle "
                                     f"occasioni segnarne {g} o meno capitava {_once(P)}."), tid, f"rit:pl:{tid}")


# ---------- incroci, precedenti, arbitro, scelta ----------

def _pair_facts(o, PP, hid, aid, names, league, cup, drop):
    """Chicche che legano le due squadre: un punto di forza dell'una contro lo stesso punto debole dell'altra."""
    min_n = 3 if cup else 4
    where = _where(league)
    teams = [q for q in PP.values() if q["n"] >= min_n]
    evq = [q for q in teams if q["ev"]]
    for a, b in ((hid, aid), (aid, hid)):
        A_, B_ = PP.get(a), PP.get(b)
        if not A_ or not B_ or A_["n"] < min_n or B_["n"] < min_n:
            return
        X, Y = names[a], names[b]
        EA, EB = A_["ev"], B_["ev"]
        if EA and EB:
            if A_["gf"] >= MIN_G and B_["ga"] >= MIN_G:
                sa, sb = EA["bf"][5] / A_["gf"], EB["ba"][5] / B_["ga"]
                ea = _rare([q["ev"]["bf"][5] / q["gf"] for q in evq if q["gf"] >= MIN_G], sa)
                eb = _rare([q["ev"]["ba"][5] / q["ga"] for q in evq if q["ga"] >= MIN_G], sb)
                if sa >= .3 and sb >= .3 and min(ea, eb) >= .3:
                    o.add("incrocio", min(ea, eb), f"Occhio al finale: {X} ha segnato {_il_pct(sa)} dei suoi gol dal 76' in poi, "
                          f"{Y} ha subito {_il_pct(sb)} dei suoi nello stesso periodo.", None, f"x-late:{a}")
                    drop |= {f"latef:{a}", f"latea:{b}"}
            for tag, text in (("head", "Gol di testa: {X} ne ha segnati {ka}, {Y} ne ha subiti {kb}."),
                              ("corner", "Calci d'angolo: {X} ha segnato {ka} gol nati da corner, {Y} ne ha subiti {kb}."),
                              ("counter", "Contropiede: {X} ha segnato {ka} gol in ripartenza, {Y} ne ha subiti {kb}."),
                              ("out", "Tiri da lontano: {X} ha segnato {ka} gol da fuori area, {Y} ne ha subiti {kb}.")):
                ka, kb = EA["tf"].get(tag, 0), EB["ta"].get(tag, 0)
                ea = _rare([q["ev"]["tf"].get(tag, 0) for q in evq], ka)
                eb = _rare([q["ev"]["ta"].get(tag, 0) for q in evq], kb)
                if ka >= 3 and kb >= 3 and min(ea, eb) >= .3:
                    o.add("incrocio", min(ea, eb), text.format(X=X, Y=Y, ka=ka, kb=kb), None, f"x-{tag}:{a}")
                    drop |= {f"tf{tag}:{a}", f"ta{tag}:{b}"}
        # serie aperte che si scontrano
        sa, sb = A_["st"], B_["st"]
        if sa["unb"] >= 4 and sb["winless"] >= 4:
            ea = _rare([q["st"]["unb"] for q in teams], sa["unb"])
            eb = _rare([q["st"]["winless"] for q in teams], sb["winless"])
            ta = f"{X} non ha ancora perso in questa stagione" if sa["unb"] == A_["n"] else f"{X} non perde da {sa['unb']} partite"
            tb = f"{Y} non ha ancora vinto" if sb["winless"] == B_["n"] else f"{Y} non vince da {sb['winless']}"
            o.add("incrocio", (ea + eb) / 2, f"{ta}, {tb}.", None, "x-serie")
            drop |= {f"grp:ris:{a}", f"grp:ris:{b}"}
        # attacco contro difesa (gol a partita)
        gpg = [q["gf"] / q["n"] for q in teams]
        gapg = [q["ga"] / q["n"] for q in teams]
        if _top(gpg, A_["gf"] / A_["n"]) == (1, 0):
            if _top(gapg, B_["ga"] / B_["n"]) == (1, 0):
                o.add("incrocio", .75, f"Il miglior attacco {where} contro la difesa più battuta: {X} ha segnato {A_['gf']} gol in "
                      f"{A_['n']} partite, {Y} ne ha subiti {B_['ga']} in {B_['n']}.", None, "x-attdif")
            elif _top(gapg, B_["ga"] / B_["n"], False) == (1, 0):
                o.add("incrocio", .7, f"Il miglior attacco {where} contro la miglior difesa: {X} ha segnato {A_['gf']} gol in "
                      f"{A_['n']} partite, {Y} ne ha subiti {B_['ga']} in {B_['n']}.", None, "x-attdif")
    A_, B_ = PP.get(hid), PP.get(aid)
    X, Y = names[hid], names[aid]
    sa, sb = A_["st"], B_["st"]
    if sa["win"] >= 3 and sb["win"] >= 3:
        e = min(_rare([q["st"]["win"] for q in teams], sa["win"]), _rare([q["st"]["win"] for q in teams], sb["win"]))
        o.add("incrocio", e, f"Si affrontano due squadre in serie: {X} vince da {sa['win']} partite di fila, {Y} da {sb['win']}.", None, "x-serie")
        drop |= {f"grp:ris:{hid}", f"grp:ris:{aid}"}
    oa, ob = A_["o25"] / A_["n"], B_["o25"] / B_["n"]
    vo = [q["o25"] / q["n"] for q in teams]
    if oa >= .7 and ob >= .7:
        o.add("incrocio", min(_rare(vo, oa), _rare(vo, ob)), f"Due squadre da gol: {X} ha avuto almeno 3 gol in {_su(A_['o25'], A_['n'])}, "
              f"{Y} in {_su(B_['o25'], B_['n'], True)}.", None, "x-o25")
        drop |= {f"o25:{hid}", f"o25:{aid}"}
    elif oa <= .25 and ob <= .25:
        o.add("incrocio", min(_rare(vo, oa, False), _rare(vo, ob, False)), f"Partite con pochi gol per entrambe: {X} ha avuto più di 2 gol in "
              f"{_su(A_['o25'], A_['n'])}, {Y} in {_su(B_['o25'], B_['n'], True)}.", None, "x-o25")
        drop |= {f"u25:{hid}", f"u25:{aid}"}


def _h2h_facts(o, extra, hid, aid, names, prev):
    hn, an = names[hid], names[aid]
    h = (extra or {}).get("h2h") or {}
    g, w = h.get("games") or 0, h.get("team") or {}
    if g:
        x, y, z = w.get("home") or 0, w.get("draws") or 0, w.get("away") or 0
        draws = f" e {y} {'è finito' if y == 1 else 'sono finiti'} in pareggio" if y else ""
        if g == 1:
            o.add("semplice", .1, "L'ultimo precedente tra le due squadre è finito in pareggio." if y else
                  f"L'ultimo precedente tra le due squadre l'ha vinto {hn if x else an}.", None, "h2h")
        elif y == g:
            o.add("precedenti", .9 if g >= 3 else .5, f"Gli ultimi {g} precedenti tra le due squadre sono finiti tutti in pareggio.", None, "h2h")
        elif g >= 4 and (x == 0 or z == 0):
            nv, vv, kv = (an, hn, x) if z == 0 else (hn, an, z)
            o.add("precedenti", .6 + .1 * (g - 4), f"Negli ultimi {g} precedenti tra le due squadre {nv} non ha mai vinto: {vv} ne ha vinti {kv}{draws}.",
                  None, "h2h")
        else:
            (wn, kw), (ln, kl) = sorted(((hn, x), (an, z)), key=lambda t: -t[1])
            o.add("precedenti", .2, f"Negli ultimi {g} precedenti {wn} ha vinto {_pl(kw, 'volta', 'volte')}, {ln} "
                  f"{_pl(kl, 'volta', 'volte') if kl else 'mai'}{draws}.", None, "h2h")
    games = sorted((r for r in prev if {r[0], r[1]} == {hid, aid}), key=lambda r: r[4])
    if games:
        res = [f"{names[r[0]]}-{names[r[1]]} {r[2]}-{r[3]}" for r in games]
        winners = {r[0] if r[2] > r[3] else r[1] if r[3] > r[2] else None for r in games}
        if len(games) >= 2 and len(winners) == 1 and None not in winners:
            win = names[winners.pop()]
            o.add("precedenti", .5, f"La scorsa stagione {win} le ha vinte {'entrambe' if len(games) == 2 else 'tutte'}: {_join(res)}.", None, "prev")
        else:
            o.add("semplice", .1, f"La scorsa stagione: {_join(res)}.", None, "prev")


def _ref_facts(o, extra, hid, aid, names, league):
    R = (extra or {}).get("referee") or {}
    ref = R.get("name")
    if not ref:
        return
    where = _where(league)
    res = R.get("res") or {}
    n = res.get("n") or 0
    if n >= 8 and res.get("base"):
        sh, b = res["h"] / n, res["base"][0]
        if abs(sh - b) >= .15:
            o.add("arbitro", abs(sh - b) / .3, f"Con {ref} arbitro le squadre di casa hanno vinto {res['h']} delle sue {n} partite {where} "
                  f"tra questa stagione e la scorsa ({_pct(sh)}): la media è {_pct(b)}.", None, "ref")
    for tid in (hid, aid):
        w, d, l = (R.get("tm") or {}).get(tid) or (0, 0, 0)
        k = w + d + l
        X = names[tid]
        if k >= 3 and w == k:
            o.add("arbitro", .75, f"{X} ha vinto tutte e {k} le partite arbitrate da {ref} {where}, tra questa stagione e la scorsa.", tid, f"ref:{tid}")
        elif k >= 3 and w == 0:
            o.add("arbitro", .6, f"{X} non ha mai vinto nelle {k} partite arbitrate da {ref} {where}, tra questa stagione e la scorsa: "
                  f"{_rec(0, d, l)}.", tid, f"ref:{tid}")
        elif k >= 2:
            o.add("semplice", .25, f"{X} con {ref} arbitro {where}: {_rec(w, d, l)} in {k} partite, tra questa stagione e la scorsa.",
                  tid, f"ref:{tid}")


def _select(items, drop):
    """Una chicca per gruppo (la più particolare), al massimo MAX_OUT, almeno MIN_SIMPLE semplici se ci sono, non più di
    MAX_TEAM particolari per squadra; in ordine dalla più particolare alla più semplice. In fondo, a parte, fino a MAX_RIT
    ritardi statistici (lv «Ritardo»)."""
    rit = sorted((it for it in items if it["kind"] == "ritardo"), key=lambda it: -it["r"])[:MAX_RIT]
    drop = drop | {k for it in rit for k in it.get("rep") or ()}
    best = {}
    for i, it in enumerate(items):
        if it["key"] in drop or (it["grp"] and f"grp:{it['grp']}" in drop):
            continue
        g = it["grp"] or f"_{i}"
        if g not in best or it["r"] > best[g]["r"]:
            best[g] = it
    items = sorted(best.values(), key=lambda it: -it["r"])
    items = [it for it in items if it["kind"] != "ritardo"]
    simple_lim = LEVELS[1][0]
    rich = [it for it in items if it["r"] >= simple_lim]
    simple = [it for it in items if it["r"] < simple_lim]
    out, per = [], collections.Counter()
    for it in rich:
        if len(out) >= MAX_OUT - min(MIN_SIMPLE, len(simple)):
            break
        if it["team"] and per[it["team"]] >= MAX_TEAM:
            continue
        out.append(it)
        per[it["team"]] += 1
    out += simple[:MAX_OUT - len(out)]
    out.sort(key=lambda it: -it["r"])
    return [{"t": it["t"], "team": it["team"], "cat": it["cat"], "r": it["r"],
             "lv": "Ritardo" if it["kind"] == "ritardo" else next(lab for lim, lab in LEVELS if it["r"] >= lim)} for it in out + rit]


def match_facts(A, hid, aid, extra=None, league="Serie A"):
    """Le chicche di una partita, dalla più particolare alla più semplice: [{"t": testo, "team": squadra o None (della
    partita), "cat": tipo, "r": particolarità 0-1, "lv": Rara/Curiosa/Semplice, o Ritardo per i ritardi statistici}]."""
    C = A.get("chic") or {}
    PP = C.get("P") or {}
    hid, aid = str(hid), str(aid)
    names = {t: A["T"][t]["team"]["name"].strip() for t in (hid, aid)}
    cup = bool(A.get("cup"))
    o, drop = _Out(), set()
    players = list((A.get("players") or {}).values())
    for tid, venue in ((hid, "home"), (aid, "away")):
        if tid in PP:
            _team_facts(o, PP, tid, venue, names[tid], league, cup, players)
            _ritardi(o, PP[tid], tid, names[tid], players, C.get("us"))
    if hid in PP and aid in PP:
        _pair_facts(o, PP, hid, aid, names, league, cup, drop)
    _h2h_facts(o, extra, hid, aid, names, C.get("prev") or [])
    _ref_facts(o, extra, hid, aid, names, league)
    return _select(o.items, drop)

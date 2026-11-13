"""Storico dei pronostici: salvataggio al calcio d'inizio, confronto con i risultati, riepiloghi.
Pezzo di model.py (diviso il 13/11/2026): si usa come model.update_history ecc., importare sempre model."""
import math
import re
import time
import unicodedata

import model
from model import market_of, predict, summary


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


def merge_history(H, other):
    """Prende da un altro storico (quello di GitHub, che gira anche col Mac spento) il pronostico al calcio d'inizio
    delle partite per cui questo ha solo quello con la formazione probabile, o nessuno, e l'altro quello con la
    formazione ufficiale: succede quando il Mac è in stop nell'ora prima della partita. Valutazioni e combo si rifanno
    (update_history). -> quante partite prese"""
    n = 0
    mine = H.setdefault("matches", {})
    for eid, o in (other.get("matches") or {}).items():
        it, f = mine.get(eid), o.get("final") or {}
        if not it or f.get("lineups") != "ufficiale" or (it.get("final") or {}).get("lineups") == "ufficiale":
            continue
        it["final"] = f
        if o.get("market"):
            it["market"] = o["market"]
        it["fromCloud"] = True
        if it.get("result"):
            it["eval"] = evaluate(f, it["result"]["hs"], it["result"]["as"])
        for k in ("evalMk", "comboEval"):   # si rifanno con il pronostico nuovo
            it.pop(k, None)
        n += 1
    return n


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


def freq_1x2(results, min_n=50):
    """Frequenze di 1, X e 2 in una lista di partite giocate (hs/as), None se sono meno di min_n."""
    r = [x for x in results or [] if x.get("hs") is not None and x.get("as") is not None]
    if len(r) < min_n:
        return None
    c = {"1": 0, "X": 0, "2": 0}
    for x in r:
        c["1" if x["hs"] > x["as"] else "X" if x["hs"] == x["as"] else "2"] += 1
    return {k: v / len(r) for k, v in c.items()}


def history_summary(H, base=None):
    done = [it for it in H.get("matches", {}).values() if it.get("eval")]
    n = len(done)
    if not n:
        return {"n": 0}
    s = lambda k: sum(1 for it in done if it["eval"][k]) / n
    # pronostico «cieco»: le frequenze 1X2 della stagione scorsa della stessa lega (server.base_1x2). Fino all'08/11/2026
    # erano quelle della Serie A per tutte le leghe; restano come riserva se la stagione scorsa manca
    base = base or {"1": .44, "X": .27, "2": .29}
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
            "brier": sum(it["eval"]["brier"] for it in done) / n, "baseBrier": base_brier, "base": base, "cal": cal,
            "players": pl if pl["n"] else None, "market": market, "combo": combo_summary(done)}

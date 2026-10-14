"""Controlli automatici dei dati di una lega, a ogni aggiornamento (sul Mac e su GitHub): cercano incoerenze tra le
parti (classifica e risultati, giocatori e squadre, letture e punteggi, pronostici, storico, allenatori) e valori fuori
scala nei pronostici dei giocatori. Non correggono niente: dicono cosa guardare. Il sito mostra il risultato.

Nati dal controllo generale del 14/10/2026: gli errori trovati quel giorno erano silenziosi (nessun crash, numeri
sbagliati), visibili solo confrontando le parti tra loro. ricerca/controllo.py li lancia sui dati salvati del Mac."""
import collections


def check_data(data, snap, hist, M):
    """-> elenco di anomalie (testi). data: cache/data.json; snap: la fotografia; hist: lo storico; M: le partite."""
    out = []
    bad = lambda *a: out.append(" ".join(str(x) for x in a))
    cup = (snap.get("league") or {}).get("cup")
    played = [e for e in data.get("played") or [] if e.get("hs") is not None and e.get("status") == "finished"]
    rows = (data.get("standings") or {}).get("total") or []
    name = {str(r["team"]["id"]): r["team"]["name"] for r in rows}
    # 1. classifica rifatta dai risultati (in coppa solo la fase campionato)
    tab = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0])   # p w d l gf ga
    for e in played:
        if cup and e.get("stage") not in (None, "league-phase"):
            continue
        h, a = str(e["home"]["id"]), str(e["away"]["id"])
        for t, gf, ga in ((h, e["hs"], e["as"]), (a, e["as"], e["hs"])):
            r = tab[t]
            r[0] += 1
            r[4] += gf
            r[5] += ga
            r[1 if gf > ga else 2 if gf == ga else 3] += 1
    for r in rows:
        t = str(r["team"]["id"])
        mine = tab.get(t, [0] * 6)
        if [r["p"], r["w"], r["d"], r["l"], r["gf"], r["ga"]] != mine:
            bad("classifica di", name[t], "diversa dai risultati:", [r["p"], r["w"], r["d"], r["l"], r["gf"], r["ga"]], "invece di", mine)
        if r["pts"] != 3 * r["w"] + r["d"]:
            bad("punti di", name[t], r["pts"], "invece di", 3 * r["w"] + r["d"], "(penalizzazione?)")
    # 2. partite doppie e giornate con una squadra due volte
    ids = collections.Counter(str(e["id"]) for lst in ("played", "next", "live") for e in data.get(lst) or [])
    for k, n in ids.items():
        if n > 1:
            bad("partita ripetuta", k, n, "volte")
    rnd = collections.defaultdict(collections.Counter)
    for e in (data.get("played") or []) + (data.get("next") or []):
        if not cup or e.get("stage") in (None, "league-phase"):
            for s in ("home", "away"):
                rnd[e.get("round")][str(e[s]["id"])] += 1
    for r_, c in rnd.items():
        twice = [name.get(t, t) for t, n in c.items() if n > 1]
        if twice:
            bad("giornata", r_, "con squadre due volte:", ", ".join(twice))
    # 3. giocatori contro squadre (i gol di chi ha cambiato squadra in stagione contano anche quelli con l'altra)
    moved = collections.defaultdict(set)
    for e in played:
        for x in (((M.get(str(e["id"])) or {}).get("box") or {}).get("players") or {}).values():
            if x.get("side") in ("home", "away"):
                moved[x.get("name")].add(str(e[x["side"]]["id"]))
    by_team = collections.defaultdict(list)
    for p in data.get("players") or []:
        by_team[str(p.get("teamId"))].append(p)
    tm = {str(r["team"]["id"]): r["p"] for r in rows}
    gf = {str(r["team"]["id"]): r["gf"] for r in rows}
    for t, ps in by_team.items():
        if t not in tm:
            if sum(p.get("minutesPlayed") or 0 for p in ps) > 0:
                bad("giocatori di una squadra che non c'è:", t, len(ps))
            continue
        if not cup:
            mins = sum(p.get("minutesPlayed") or 0 for p in ps)
            exp = tm[t] * 990
            if exp and not .93 <= mins / exp <= 1.07:
                bad("minuti dei giocatori di", name[t], round(mins), "attesi circa", exp)
            g = sum(p.get("goals") or 0 for p in ps)
            g_stay = sum(p.get("goals") or 0 for p in ps if len(moved.get(p["name"]) or ()) <= 1)
            if g_stay > gf[t] or gf[t] - g > max(2, .12 * gf[t]):
                bad("gol dei giocatori di", name[t], g, "contro i gol della squadra", gf[t])
        for p in ps:
            if (p.get("minutesPlayed") or 0) > (tm[t] if not cup else 20) * 90 + 60:
                bad("minuti impossibili:", p["name"], p.get("minutesPlayed"), "in", tm.get(t), "partite")
        for n_, c in collections.Counter(p["name"] for p in ps).items():
            if c > 1:
                bad("giocatore doppio in", name.get(t, t) + ":", n_)
    # 4. pronostici
    for f in snap.get("fixtures") or []:
        s = f["p1"] + f["px"] + f["p2"]
        if abs(s - 1) > .01 or not (0.1 < f["lh"] < 5 and 0.1 < f["la"] < 5):
            bad("pronostico strano", f["id"], round(s, 3), f["lh"], f["la"])
    # 5. letture contro risultati
    for k, r in (snap.get("reads") or {}).items():
        if len(r.get("goals") or []) != r["hs"] + r["as"]:
            bad("lettura", k, f"{r['hs']}-{r['as']}", "con", len(r.get("goals") or []), "gol")
        if min(r["xg"]) < 0 or max(r["xg"]) > 8:
            bad("xG strani nella lettura", k, r["xg"])
    # 6. storico: esito giusto
    for k, it in ((hist or {}).get("matches") or {}).items():
        res, ev = it.get("result"), it.get("eval") or {}
        if res and ev.get("outcome"):
            o = "1" if res["hs"] > res["as"] else "X" if res["hs"] == res["as"] else "2"
            if ev["outcome"] != o:
                bad("storico: esito sbagliato", k)
    # 7. allenatori
    no = [t["name"] for t in (snap.get("teams") or {}).values() if not t.get("coach") and not t.get("vacant")]
    if no:
        bad("squadre senza allenatore:", ", ".join(no))
    return out


def check_predictions(snap):
    """Valori fuori scala nei pronostici dei giocatori (caso Muriqi del 14/10/2026: 6,7 falli e 73% di giallo per
    una base senza falli): più di 4 falli, giallo oltre il 45%, gol oltre il 65%, più di 6 tiri, un giocatore con più
    del 40% dei falli della squadra. -> elenco di testi."""
    out = []
    teams = snap.get("teams") or {}
    nm = lambda t: (teams.get(str(t)) or {}).get("name") or t
    for f in snap.get("fixtures") or []:
        P = f.get("P") or {}
        for side in ("home", "away"):
            ps = (P.get("players") or {}).get(side) or []
            tf = sum(p.get("fouls") or 0 for p in ps) or 1
            for p in ps:
                why = []
                if (p.get("fouls") or 0) > 4.0:
                    why.append(f"{p['fouls']:.1f} falli")
                if (p.get("pYellow") or 0) > .45:
                    why.append(f"giallo al {p['pYellow']:.0%}")
                if (p.get("pGoal") or 0) > .65:
                    why.append(f"gol al {p['pGoal']:.0%}")
                if (p.get("shots") or 0) > 6:
                    why.append(f"{p['shots']:.1f} tiri")
                if tf > 3 and (p.get("fouls") or 0) / tf > .4:
                    why.append(f"{(p.get('fouls') or 0) / tf:.0%} dei falli della squadra")
                if why:
                    out.append(f"{nm(f['home'])}-{nm(f['away'])}: {p.get('name')} con " + ", ".join(why))
    return out


def check_links(data, links=None):
    """Collegamenti tra le fonti che sembrano sbagliati: minuti molto diversi tra ESPN e Understat o Opta (oltre 150 e
    oltre il 40%: il 14/10/2026 il collegamento con i minuti, partito con troppe poche partite, aveva preso Jannik
    Schuster per Kevin Schade), e i casi in cui nome e minuti indicano due giocatori diversi."""
    out = []
    for s in (data.get("compare") or {}).get("sources") or []:
        if s.get("src") not in ("Understat", "Opta"):
            continue
        for x in s.get("diff") or []:
            for k, a, b in x["d"]:
                if k == "minuti" and a is not None and b is not None and abs(a - b) > max(150, .4 * max(a, b)):
                    out.append(f"{x['name']}: {a:.0f} minuti per ESPN e {b:.0f} per {s['src']} (collegamento sbagliato?)")
    out += [f"nome e minuti non tornano: {c}" for c in (links or {}).get("conflicts") or []]
    return out


def summary(data, snap, hist, M, links=None):
    """Tutti i controlli, per la fotografia: {"ok", "n", "data", "pred", "compare", "links"}."""
    d = check_data(data, snap, hist, M) + check_links(data, links)
    pr = check_predictions(snap)
    cmp_ = data.get("compare") or {}
    return {"ok": not d and not pr, "n": len(d) + len(pr), "data": d[:30], "pred": pr[:30],
            "compare": [{k: s.get(k) for k in ("src", "n", "same", "nDiff", "diff")} for s in cmp_.get("sources") or []],
            "links": links}

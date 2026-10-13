"""Forza delle squadre europee su una scala unica, per la Champions League (dove si incontrano squadre di campionati
diversi e le statistiche di un solo campionato non si possono confrontare).

Modello di Poisson: ogni squadra ha un attacco e una difesa; i gol attesi in casa sono
exp(media + campo + attacco di casa + difesa ospite). Le partite dei campionati e delle coppe europee (preliminari
compresi) si pesano per quanto sono recenti (emivita di un anno). Ogni squadra viene avvicinata alla media del suo
campionato, così chi ha giocato poco non finisce alla media di tutta Europa; le coppe europee collegano i campionati.
Il vantaggio del campo nelle coppe europee è separato da quello dei campionati (è più alto: trasferte lunghe).

Prova all'indietro del 13/10/2026 sulle 378 partite di Champions 2024/25 e 2025/26, ognuna prevista solo con le
partite giocate prima: log loss 0,898 contro 1,014 delle frequenze fisse di 1, X e 2 (esiti azzeccati 59%). Senza
le medie di campionato 0,917; emivita di sei mesi 0,903; una media dei gol a parte per le coppe peggiora.

Solo funzioni pure: i dati (calendari mensili di ESPN) li scarica server.py.
"""
import math
from collections import defaultdict
from datetime import datetime, timezone

# campionati e coppe che servono: quelli delle squadre di Champions che ESPN copre, e le coppe europee
COMPS = ["eng.1", "esp.1", "ita.1", "ger.1", "fra.1", "por.1", "ned.1", "bel.1", "tur.1", "aut.1", "gre.1", "sco.1", "sui.1",
         "den.1", "swe.1", "nor.1", "cyp.1", "rou.1", "rus.1",
         "uefa.champions", "uefa.champions_qual", "uefa.europa", "uefa.europa_qual", "uefa.europa.conf",
         "uefa.europa.conf_qual", "uefa.super_cup"]
HALF_LIFE = 365       # giorni
K_TEAM = 4.0          # quanto ogni squadra viene avvicinata alla media del suo campionato
K_LEAGUE = 1.0        # quanto le medie dei campionati vengono avvicinate a zero
WINDOW = 3.2 * 365    # partite più vecchie di così non contano


def compact(j, comp):
    """Calendario mensile di ESPN -> partite compatte."""
    out = []
    for e in j.get("events") or []:
        c = (e.get("competitions") or [{}])[0]
        st = ((c.get("status") or e.get("status") or {}).get("type") or {})
        side = {x.get("homeAway"): x for x in c.get("competitors") or []}
        if "home" not in side or "away" not in side:
            continue
        h, a = side["home"], side["away"]
        sc = lambda x: int(x["score"]) if str(x.get("score", "")).isdigit() else None
        out.append({"id": str(e["id"]), "date": e.get("date"), "comp": comp, "done": bool(st.get("completed")),
                    "neutral": bool(c.get("neutralSite")) or (e.get("season") or {}).get("slug") == "final",
                    "h": str(h["team"]["id"]), "hn": h["team"].get("displayName"), "a": str(a["team"]["id"]),
                    "an": a["team"].get("displayName"), "hs": sc(h), "as": sc(a)})
    return out


def prepare(matches):
    """Partite finite, in ordine, con la data in secondi e i segni per le coppe; squadra -> campionato."""
    done = []
    for m in matches:
        if not m.get("done") or m.get("hs") is None or m.get("as") is None or not m.get("date"):
            continue
        try:
            t = datetime.strptime(m["date"][:16], "%Y-%m-%dT%H:%M").replace(tzinfo=timezone.utc).timestamp()
        except ValueError:
            continue
        eu = m["comp"].startswith("uefa.")
        done.append(dict(m, t=t, eu=eu, neu=m.get("neutral") or m["comp"] == "uefa.super_cup"))
    done.sort(key=lambda m: m["t"])
    count = defaultdict(lambda: defaultdict(int))
    for m in done:
        if not m["eu"]:
            count[m["h"]][m["comp"]] += 1
            count[m["a"]][m["comp"]] += 1
    group = {t: max(c, key=c.get) for t, c in count.items()}
    return done, group


def fit(done, group, now, prev=None, iters=40):
    """Stima attacco e difesa di tutte le squadre con le partite finite prima di `now`. prev: stima precedente da
    cui partire (bastano poche iterazioni). -> {"mu", "h", "he", "A", "D", "GA", "GD", "group", "n"}."""
    P = {"mu": math.log(1.35), "h": .2, "he": .3, "A": {}, "D": {}, "GA": {}, "GD": {}}
    if prev:
        P.update(mu=prev["mu"], h=prev["h"], he=prev["he"], A=dict(prev["A"]), D=dict(prev["D"]),
                 GA=dict(prev["GA"]), GD=dict(prev["GD"]))
    hl = HALF_LIFE * 86400
    rows = [(m, .5 ** ((now - m["t"]) / hl)) for m in done if m["t"] < now and now - m["t"] < WINDOW * 86400]
    if not rows:
        return None
    teams = {t for m, _ in rows for t in (m["h"], m["a"])}
    g_of = {t: group.get(t, "altro") for t in teams}
    for t in teams:
        P["A"].setdefault(t, 0.0)
        P["D"].setdefault(t, 0.0)
    mem = defaultdict(list)
    for t in teams:
        mem[g_of[t]].append(t)
    for g in mem:
        P["GA"].setdefault(g, 0.0)
        P["GD"].setdefault(g, 0.0)
    by_team = defaultdict(list)
    for i, (m, w) in enumerate(rows):
        by_team[m["h"]].append(i)
        by_team[m["a"]].append(i)

    def lams():
        out = []
        for m, w in rows:
            hh = 0.0 if m["neu"] else (P["he"] if m["eu"] else P["h"])
            out.append((math.exp(P["mu"] + hh + P["A"][m["h"]] + P["D"][m["a"]]),
                        math.exp(P["mu"] + P["A"][m["a"]] + P["D"][m["h"]])))
        return out

    for _ in range(iters):
        # a blocchi, ricalcolando i gol attesi tra un blocco e l'altro (aggiornare tutto insieme fa divergere)
        for kind in ("A", "D"):
            lam = lams()
            par, gpar = P[kind], P["G" + kind]
            for t in teams:
                g = hs = 0.0
                for i in by_team[t]:
                    (m, w), (lh, la) = rows[i], lam[i]
                    home = m["h"] == t
                    if kind == "A":
                        g += w * ((m["hs"] - lh) if home else (m["as"] - la))
                        hs += w * (lh if home else la)
                    else:
                        g += w * ((m["as"] - la) if home else (m["hs"] - lh))
                        hs += w * (la if home else lh)
                par[t] += (g - K_TEAM * (par[t] - gpar[g_of[t]])) / (hs + K_TEAM)
            for g, ts in mem.items():
                gpar[g] = K_TEAM * sum(par[t] for t in ts) / (K_TEAM * len(ts) + K_LEAGUE)
        lam = lams()
        P["mu"] += math.log(sum(w * (m["hs"] + m["as"]) for m, w in rows) / sum(w * (l[0] + l[1]) for (m, w), l in zip(rows, lam)))
        for key, sel in (("h", lambda m: not m["neu"] and not m["eu"]), ("he", lambda m: not m["neu"] and m["eu"])):
            lam = lams()
            num = sum(w * m["hs"] for (m, w), l in zip(rows, lam) if sel(m))
            den = sum(w * l[0] for (m, w), l in zip(rows, lam) if sel(m))
            if num and den:
                P[key] += math.log(num / den) / 2
        ma = sum(P["A"][t] for t in teams) / len(teams)
        md = sum(P["D"][t] for t in teams) / len(teams)
        for t in teams:
            P["A"][t] -= ma
            P["D"][t] -= md
        for g in mem:
            P["GA"][g] -= ma
            P["GD"][g] -= md
        P["mu"] += ma + md
    P["group"] = g_of
    P["n"] = {t: round(sum(rows[i][1] for i in by_team[t]), 2) for t in teams}   # partite «pesate» di ogni squadra
    return P


def effect(P, t, kind):
    """Attacco ("A") o difesa ("D") di una squadra; chi non ha partite prende la media del suo campionato."""
    v = P[kind].get(t)
    if v is None:
        v = P["G" + kind].get((P.get("group") or {}).get(t, "altro"), P["G" + kind].get("altro", 0.0))
    return v


def lambdas(P, home, away, europe=True, neutral=False):
    """Gol attesi delle due squadre in una partita."""
    hh = 0.0 if neutral else (P["he"] if europe else P["h"])
    return (math.exp(P["mu"] + hh + effect(P, home, "A") + effect(P, away, "D")),
            math.exp(P["mu"] + effect(P, away, "A") + effect(P, home, "D")))


LEAGUE_IT = {"eng.1": "Premier League", "esp.1": "Liga", "ita.1": "Serie A", "ger.1": "Bundesliga", "fra.1": "Ligue 1",
             "por.1": "Portogallo", "ned.1": "Olanda", "bel.1": "Belgio", "tur.1": "Turchia", "aut.1": "Austria",
             "gre.1": "Grecia", "sco.1": "Scozia", "sui.1": "Svizzera", "den.1": "Danimarca", "swe.1": "Svezia",
             "nor.1": "Norvegia", "cyp.1": "Cipro", "rou.1": "Romania", "rus.1": "Russia", "altro": "campionato non coperto da ESPN"}

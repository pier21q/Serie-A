"""Statistiche di squadre e giocatori da fonti che rispondono senza blocchi.

- ESPN, cioè i dati ufficiali delle partite: per squadra tiri, possesso, passaggi, cross, lanci, contrasti,
  intercetti, respinte, falli, cartellini, angoli, parate; per giocatore gol, assist, tiri, tiri in porta,
  falli fatti e subiti, cartellini, parate.
- Understat: xG, xA, xG concessi, pressing (PPDA), palloni giocati vicino all'area (deep), passaggi chiave, minuti.
- Fantacalcio.it: media voto e fantamedia.

Qui ci sono solo le funzioni che leggono i dati e li sommano: le richieste le fa server.py.
"""
import html
import json
import re

UNDERSTAT = "https://understat.com/getLeagueData/Serie_A/{year}"
UNDERSTAT_REF = "https://understat.com/league/Serie_A/{year}"
FC_STATS = "https://www.fantacalcio.it/statistiche-serie-a"

BOX_TEAM = {"foulsCommitted": "fouls", "yellowCards": "yellowCards", "redCards": "redCards", "offsides": "offsides",
            "wonCorners": "corners", "saves": "saves", "possessionPct": "possession", "totalShots": "shots",
            "shotsOnTarget": "shotsOnTarget", "penaltyKickGoals": "penaltyGoals", "penaltyKickShots": "penalties",
            "accuratePasses": "accuratePasses", "totalPasses": "totalPasses", "accurateCrosses": "accurateCrosses",
            "totalCrosses": "totalCrosses", "totalLongBalls": "totalLongBalls", "accurateLongBalls": "accurateLongBalls",
            "blockedShots": "blockedShots", "effectiveTackles": "tacklesWon", "totalTackles": "tackles",
            "interceptions": "interceptions", "effectiveClearance": "clearances"}
BOX_PLAYER = {"totalGoals": "goals", "goalAssists": "assists", "totalShots": "shots", "shotsOnTarget": "sot",
              "foulsCommitted": "fouls", "foulsSuffered": "fouled", "yellowCards": "yc", "redCards": "rc",
              "offsides": "off", "saves": "saves", "goalsConceded": "gc", "ownGoals": "og", "appearances": "app",
              "subIns": "sub"}


def num(v):
    try:
        return float(str(v).replace(",", "."))
    except (TypeError, ValueError):
        return None


def _minute(k):
    v = (k.get("clock") or {}).get("value")
    return min(90.0, float(v) / 60) if v is not None else None


# ---------- ESPN: una partita ----------

def box_from_summary(j):
    """Riepilogo ESPN di una partita finita -> statistiche compatte delle due squadre e dei giocatori."""
    ros = {r.get("homeAway"): r for r in j.get("rosters") or []}
    side_of = {str((r.get("team") or {}).get("id")): s for s, r in ros.items()}
    out = {"home": {}, "away": {}, "players": {}}
    for t in (j.get("boxscore") or {}).get("teams") or []:
        s = side_of.get(str((t.get("team") or {}).get("id"))) or t.get("homeAway")
        if s not in ("home", "away"):
            continue
        out[s] = {BOX_TEAM[x["name"]]: num(x.get("displayValue")) for x in t.get("statistics") or [] if x.get("name") in BOX_TEAM}
    if not out["home"] or not out["away"]:
        return None
    for s in ("home", "away"):
        out[s]["headedGoals"] = 0
    # minuti giocati: dall'ingresso all'uscita (sostituzione o espulsione)
    enter, leave = {}, {}
    for k in j.get("keyEvents") or []:
        typ = ((k.get("type") or {}).get("text") or "").lower()
        ps = [str((p.get("athlete") or {}).get("id")) for p in k.get("participants") or []]
        s = side_of.get(str((k.get("team") or {}).get("id")))
        if k.get("scoringPlay") and s and "header" in typ and "own" not in typ:
            out[s]["headedGoals"] += 1
        if typ == "substitution" and len(ps) >= 2:
            enter[ps[0]], leave[ps[1]] = _minute(k), _minute(k)
        elif "red card" in typ and ps:
            leave[ps[0]] = _minute(k)
    for s, r in ros.items():
        for a in r.get("roster") or []:
            pid = str((a.get("athlete") or {}).get("id"))
            st = {BOX_PLAYER[x["name"]]: x.get("value") for x in a.get("stats") or [] if x.get("name") in BOX_PLAYER}
            if not st.get("app"):
                continue
            start = 0.0 if a.get("starter") else enter.get(pid)
            end = leave.get(pid, 90.0)
            st.update(side=s, start=bool(a.get("starter")), num=a.get("jersey"),
                      pos=((a.get("position") or {}).get("abbreviation") or "").upper(),
                      min=max(1.0, round((end if end is not None else 90.0) - (start if start is not None else 75.0))),
                      name=(a.get("athlete") or {}).get("displayName"))
            out["players"][pid] = {k: v for k, v in st.items() if v not in (None, 0, 0.0) or k in ("side", "start", "min")}
    return out


# ---------- Understat ----------

def understat_parse(j):
    """Dati della stagione di Understat -> squadre (partita per partita) e giocatori (totali della stagione)."""
    teams = {}
    for t in (j.get("teams") or {}).values():
        teams[t["title"]] = t.get("history") or []
    players = []
    for p in j.get("players") or []:
        q = {"usId": str(p["id"]), "name": html.unescape(p.get("player_name") or ""), "team": html.unescape(p.get("team_title") or ""),
             "usPos": p.get("position")}
        for src, dst in (("games", "appearances"), ("time", "minutesPlayed"), ("goals", "goals"), ("assists", "assists"),
                         ("xG", "expectedGoals"), ("xA", "expectedAssists"), ("shots", "totalShots"), ("key_passes", "keyPasses"),
                         ("yellow_cards", "yellowCards"), ("red_cards", "redCards"), ("npg", "npg"), ("npxG", "npxG"),
                         ("xGChain", "xGChain"), ("xGBuildup", "xGBuildup")):
            q[dst] = num(p.get(src))
        players.append(q)
    return {"teams": teams, "players": players}


# ---------- Fantacalcio.it ----------

def parse_fc_stats(page):
    """Pagina delle statistiche di Fantacalcio.it -> media voto, fantamedia, partite a voto, ruolo per giocatore."""
    out = []
    for row in re.findall(r'<tr class="player-row"(.*?)</tr>', page, re.S):
        link = re.search(r'href="https://www\.fantacalcio\.it/serie-a/squadre/([^/]+)/[^/]+/(\d+)"', row)
        name = re.search(r'class="player-name player-link"[^>]*>\s*<span>(.*?)</span>', row, re.S)
        role = re.search(r'data-filter-role-classic="(\w)"', row)
        if not (link and name):
            continue
        cell = lambda key: (re.search(r'data-col-key="%s"[^>]*>(.*?)</td>' % key, row, re.S) or [None, None])[1]
        val = lambda key: num(re.sub(r"<[^>]+>|\s", "", cell(key) or "")) if cell(key) is not None else None
        out.append({"fcId": link.group(2), "teamSlug": link.group(1), "name": html.unescape(name.group(1).strip()),
                    "role": role.group(1) if role else None, "pv": val("pg"), "mv": val("mv"), "fm": val("mfv"),
                    "gol": val("gol"), "ass": val("ass"), "amm": val("amm"), "esp": val("esp")})
    return out


# ---------- stagione: somme per squadra e per giocatore ----------

SUM_KEYS = ["fouls", "yellowCards", "redCards", "offsides", "corners", "saves", "shots", "shotsOnTarget", "penaltyGoals",
            "penalties", "accuratePasses", "totalPasses", "accurateCrosses", "totalCrosses", "totalLongBalls",
            "accurateLongBalls", "blockedShots", "tacklesWon", "tackles", "interceptions", "clearances", "headedGoals"]
AGAINST = {"shots": "shotsAgainst", "shotsOnTarget": "shotsOnTargetAgainst", "corners": "cornersAgainst",
           "accurateCrosses": "crossesSuccessfulAgainst", "fouls": "freeKicks", "headedGoals": "headedGoalsAgainst",
           "accuratePasses": "accuratePassesAgainst"}


def team_season(results, boxes, us_teams, team_of_title, us_players=None):
    """Statistiche di ogni squadra: somme delle partite (ESPN) e dei dati Understat.
    results: partite finite con id, home/away (id squadra), hs, as. boxes: {id partita: box}.
    team_of_title: nome Understat -> id squadra."""
    T = {}

    def get(tid):
        return T.setdefault(tid, {"matches": 0, "goalsScored": 0, "goalsConceded": 0, "cleanSheets": 0, "_poss": 0.0})

    for e in results:
        b = boxes.get(str(e["id"]))
        if e.get("hs") is None or not b:
            continue
        for s, o, gf, ga in (("home", "away", e["hs"], e["as"]), ("away", "home", e["as"], e["hs"])):
            t = get(str(e[s]["id"]))
            t["matches"] += 1
            t["goalsScored"] += gf
            t["goalsConceded"] += ga
            t["cleanSheets"] += ga == 0
            t["_poss"] += b[s].get("possession") or 50
            for k in SUM_KEYS:
                t[k] = t.get(k, 0) + (b[s].get(k) or 0)
            for k, dst in AGAINST.items():
                t[dst] = t.get(dst, 0) + (b[o].get(k) or 0)
    for title, hist in (us_teams or {}).items():
        tid = team_of_title(title)
        if not tid or tid not in T:
            continue
        t = T[tid]
        for h in hist:
            for src, dst in (("xG", "expectedGoals"), ("xGA", "expectedGoalsAgainst"), ("npxG", "npxG"), ("npxGA", "npxGA"),
                             ("deep", "deep"), ("deep_allowed", "deepAllowed"), ("xpts", "xpts")):
                t[dst] = t.get(dst, 0) + (num(h.get(src)) or 0)
            t["_ppdaAtt"] = t.get("_ppdaAtt", 0) + (num((h.get("ppda") or {}).get("att")) or 0)
            t["_ppdaDef"] = t.get("_ppdaDef", 0) + (num((h.get("ppda") or {}).get("def")) or 0)
            t["usMatches"] = t.get("usMatches", 0) + 1
    # passaggi chiave: somma dei giocatori Understat (chi ha giocato in due squadre non si può dividere)
    for p in us_players or []:
        tid = team_of_title(p["team"]) if "," not in (p.get("team") or "") else None
        if tid in T and p.get("keyPasses") is not None:
            T[tid]["keyPasses"] = T[tid].get("keyPasses", 0) + p["keyPasses"]
    for t in T.values():
        n = t["matches"] or 1
        t["averageBallPossession"] = t.pop("_poss") / n
        t["accuratePassesPercentage"] = 100 * t["accuratePasses"] / t["totalPasses"] if t.get("totalPasses") else None
        if t.get("_ppdaDef"):
            t["ppda"] = t["_ppdaAtt"] / t["_ppdaDef"]
        t.pop("_ppdaAtt", None)
        t.pop("_ppdaDef", None)
        # i dati Understat possono essere indietro di qualche partita: si riportano allo stesso numero di partite
        um = t.get("usMatches")
        if um and um != t["matches"]:
            for k in ("expectedGoals", "expectedGoalsAgainst", "npxG", "npxGA", "deep", "deepAllowed", "xpts"):
                if t.get(k) is not None:
                    t[k] = t[k] / um * t["matches"]
    return T


def player_season(results, boxes):
    """Totali di ogni giocatore dalle partite ESPN: {id ESPN: totali, con squadra e ruolo dell'ultima partita}."""
    P = {}
    for e in sorted(results, key=lambda e: e["start"]):
        b = boxes.get(str(e["id"]))
        if not b:
            continue
        for pid, st in (b.get("players") or {}).items():
            p = P.setdefault(pid, {"espnId": pid, "appearances": 0, "matchesStarted": 0, "minutesEspn": 0})
            p["appearances"] += 1
            p["matchesStarted"] += bool(st.get("start"))
            p["minutesEspn"] += st.get("min") or 0
            p["teamId"] = str(e[st["side"]]["id"])
            p["name"] = st.get("name") or p.get("name")
            if st.get("pos") and st["pos"] != "SUB":
                p["espnPos"] = st["pos"]
            if st.get("num"):
                p["num"] = st["num"]
            for src, dst in (("goals", "goalsEspn"), ("assists", "assistsEspn"), ("shots", "shotsEspn"), ("sot", "shotsOnTarget"),
                             ("fouls", "fouls"), ("fouled", "wasFouled"), ("yc", "yellowCardsEspn"), ("rc", "redCardsEspn"),
                             ("off", "offsides"), ("saves", "saves"), ("gc", "goalsConceded"), ("og", "ownGoals")):
                p[dst] = p.get(dst, 0) + (st.get(src) or 0)
            if st.get("start") and st.get("side"):
                gc = e["as"] if st["side"] == "home" else e["hs"]
                if (st.get("pos") == "G") and gc == 0 and (st.get("min") or 0) >= 60:
                    p["cleanSheet"] = p.get("cleanSheet", 0) + 1
    return P

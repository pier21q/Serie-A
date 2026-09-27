"""Fonti per i dati di ogni partita e per gli allenatori.

- fantacalcio.it: probabili formazioni con le percentuali, squalificati, diffidati, infortunati, in dubbio
- Wikipedia: allenatori della stagione (e di quella scorsa, per sapere chi è nuovo); in inglese i cambi di
  allenatore con le date, spesso aggiornati prima (Fantacalcio.it, Lega Serie A ed ESPN arrivano dopo o non li hanno)
- ESPN: precedenti tra le squadre, arbitro designato e cartellini delle partite (per le statistiche degli arbitri)

Qui ci sono solo le funzioni che leggono le pagine: le richieste le fa server.py.
"""
import html
import re
import unicodedata
from datetime import datetime, timezone

FC_PROBABILI = "https://www.fantacalcio.it/probabili-formazioni-serie-a"
WIKI = "https://it.wikipedia.org/wiki/Serie_A_{a}-{b}"
WIKI_EN = "https://en.wikipedia.org/w/api.php"
WIKI_EN_TITLE = "{a}–{b:02d} Serie A"   # "2026–27 Serie A"
COME = {"sacked": "esonero", "mutual consent": "risoluzione consensuale", "resigned": "dimissioni",
        "end of contract": "fine del contratto", "end of caretaker": "fine dell'interim", "retired": "ritiro",
        "signed by": "passato a un'altra squadra", "health": "motivi di salute"}
MESI_EN = {m: i for i, m in enumerate(("january", "february", "march", "april", "may", "june", "july", "august",
                                       "september", "october", "november", "december"), 1)}


def _text(s):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", s or ""))).strip()


# ---------- fantacalcio.it ----------

def _pills(block):
    out = []
    for li in re.findall(r'<li class="player-item[^"]*"[^>]*>(.*?)</li>', block, re.S):
        name = re.search(r'<a class="player-name[^>]*>\s*<span>(.*?)</span>', li, re.S)
        if not name:
            continue
        role = re.search(r'class="role" data-value="(\w)"', li)
        pct = re.search(r'aria-valuenow="(\d+)"', li)
        out.append({"name": _text(name.group(1)), "role": role.group(1) if role else None,
                    "pct": int(pct.group(1)) if pct else None})
    return out


def _names(part):
    """Giocatori di un riquadro (squalificati, infortunati...), con la descrizione se c'è."""
    out = []
    for m in re.finditer(r'<a class="player-name[^>]*>\s*<span>(.*?)</span>\s*</a>\s*(?:<p class="description">(.*?)</p>)?',
                         part, re.S):
        out.append({"name": _text(m.group(1)), "desc": _text(m.group(2)) or None})
    return out


def _section(seg, cls):
    m = re.search(r'<section class="%s">(.*?)</section>' % cls, seg, re.S)
    if not m:
        return [[], []]
    parts = m.group(1).split('<div class="content">')[1:]
    res = [_names(p) for p in parts[:2]]
    return res + [[]] * (2 - len(res))


def parse_probabili(page):
    """Pagina delle probabili formazioni -> una voce per partita, con le due squadre in ordine casa/trasferta."""
    matches = []
    for seg in page.split('class="match-info"')[1:]:
        cards = seg.split('class="card team-card')[1:3]
        if len(cards) < 2:
            continue
        date = re.search(r'class="match-date">(.*?)<', seg)
        upd = re.search(r'Ultimo aggiornamento <span class="date">(.*?)</span>', seg)
        extra = {k: _section(seg, cls) for k, cls in (("suspended", "suspendeds"), ("cautioned", "cautioneds"),
                                                      ("injured", "injureds"), ("doubtful", "dubts"))}
        sides = []
        for i, c in enumerate(cards):
            team = re.search(r'class="h6 team-name">(.*?)<', c)
            form = re.search(r'class="h6 team-formation">(.*?)<', c)
            st = c.split('class="player-list starters"')[1] if 'class="player-list starters"' in c else ""
            st, _, bench = st.partition('class="player-list reserves"')
            side = {"team": _text(team.group(1)) if team else "", "formation": _text(form.group(1)) if form else None,
                    "starters": _pills(st), "bench": _pills(bench)}
            side.update({k: v[i] for k, v in extra.items()})
            sides.append(side)
        if all(s["team"] for s in sides) and all(len(s["starters"]) == 11 for s in sides):
            matches.append({"date": _text(date.group(1)) if date else None,
                            "updated": _text(upd.group(1)) if upd else None, "home": sides[0], "away": sides[1]})
    return matches


def lines_positions(formation, starters):
    """Ruolo in campo (G/D/M/F) di ogni titolare: portiere, poi le linee del modulo dalla difesa all'attacco.
    Nella pagina i titolari sono in quest'ordine, ogni linea da destra a sinistra (come le formazioni ufficiali)."""
    try:
        lines = [int(x) for x in (formation or "").split("-")]
    except ValueError:
        lines = []
    if sum(lines) != 10 or len(starters) != 11:
        by_role = {"p": "G", "d": "D", "c": "M", "a": "F"}
        return [by_role.get(p.get("role"), "M") for p in starters], False
    pos = ["G"]
    for i, n in enumerate(lines):
        pos += ["D" if i == 0 else "F" if i == len(lines) - 1 else "M"] * n
    return pos, True


# ---------- Wikipedia ----------

def parse_allenatori(page):
    """Tabella 'Allenatori e primatisti' -> {squadra: [{"name", "from", "to"}]}: gli allenatori della stagione
    in ordine, con le giornate in cui sono stati in panchina (to = None se è ancora lì)."""
    for t in re.findall(r'<table class="wikitable.*?</table>', page, re.S):
        rows = re.findall(r"<tr.*?</tr>", t, re.S)
        cells = lambda r: [_text(c) for c in re.findall(r"<t[hd][^>]*>(.*?)</t[hd]>", r, re.S)]
        head = cells(rows[0]) if rows else []
        if "Allenatore" in head and "Squadra" in head:
            ci, ti = head.index("Allenatore"), head.index("Squadra")
            out = {}
            for r in rows[1:]:
                c = [re.sub(r"\[[^\]]*\]", "", x).strip() for x in cells(r)]
                if len(c) > max(ci, ti) and c[ti] and c[ci]:
                    out[c[ti]] = parse_tenures(c[ci])
            return out
    return {}


def parse_tenures(cell):
    """"Igor Tudor (1ª-8ª) Massimo Brambilla (9ª) Luciano Spalletti (10ª-)" -> allenatori con le giornate."""
    out = []
    for m in re.finditer(r"([^()]+?)\s*(?:\(([^)]*)\)|$)", cell):
        name = re.sub(r"^[,/\s]+|[,/\s]+$", "", m.group(1))
        if not name:
            continue
        rng = m.group(2) or ""
        nums = [int(n) for n in re.findall(r"\d+", rng)]
        fr = nums[0] if nums else None
        to = nums[1] if len(nums) > 1 else (None if "-" in rng or not nums else nums[0])
        out.append({"name": name, "from": fr, "to": to})
    if out:
        out[-1]["to"] = out[-1]["to"] if len(out) > 1 or out[-1]["from"] else None
    return out


def coach_at(tenures, rnd):
    """Allenatore in panchina in una certa giornata (l'ultimo se la giornata non è nota)."""
    if not tenures:
        return None
    if rnd:
        for t in tenures:
            if (t["from"] or 1) <= rnd <= (t["to"] or 99):
                return t["name"]
    return tenures[-1]["name"]


def table_grid(table):
    """Righe di una tabella HTML come liste di testi, ripetendo le celle unite (rowspan e colspan)."""
    grid, carry = [], {}   # carry: colonna -> (testo, righe che restano)
    for r in re.findall(r"<tr[^>]*>(.*?)</tr>", table, re.S):
        cells = re.findall(r"<t[hd]([^>]*)>(.*?)</t[hd]>", r, re.S)
        row, col, k = [], 0, 0
        while k < len(cells) or col in carry:
            if col in carry:
                text, left = carry.pop(col)
                if left > 1:
                    carry[col] = (text, left - 1)
            else:
                attrs, body = cells[k]
                k += 1
                text = re.sub(r"\[[^\]]*\]", "", _text(body)).strip()
                wide = re.search(r'colspan="?(\d+)', attrs)
                down = re.search(r'rowspan="?(\d+)', attrs)
                for _ in range(int(wide.group(1)) - 1 if wide else 0):
                    row.append(text)
                    col += 1
                if down and int(down.group(1)) > 1:
                    carry[col] = (text, int(down.group(1)) - 1)
            row.append(text)
            col += 1
        grid.append(row)
    return grid


def _data_en(s):
    m = re.search(r"(\d{1,2}) ([A-Za-z]+) (\d{4})", s or "")
    if not m or m.group(2).lower() not in MESI_EN:
        return None
    return int(datetime(int(m.group(3)), MESI_EN[m.group(2).lower()], int(m.group(1)), 12, tzinfo=timezone.utc).timestamp())


def parse_cambi_en(page):
    """Tabella «Managerial changes» di Wikipedia in inglese -> cambi di allenatore della stagione, in ordine:
    [{"team", "out", "how", "left" (data), "in" (None se non è ancora stato nominato), "since" (data)}]."""
    clean = lambda s: re.sub(r"\s*\((?:caretaker|interim)\)", "", s or "", flags=re.I).strip()
    for t in re.findall(r'<table class="wikitable.*?</table>', page, re.S):
        grid = table_grid(t)
        head = [h.lower() for h in grid[0]] if grid else []
        col = lambda key: next((i for i, h in enumerate(head) if key in h), None)
        it, io, ih, il, ii, isn = (col(k) for k in ("team", "outgoing", "manner", "vacancy", "incoming", "appointment"))
        if None in (it, io, ii):
            continue
        cell = lambda g, i: g[i] if i is not None and i < len(g) else ""
        out = []
        for g in grid[1:]:
            if not cell(g, it) or not cell(g, io):
                continue
            how = cell(g, ih).lower()
            out.append({"team": cell(g, it), "out": clean(cell(g, io)), "how": next((v for k, v in COME.items() if k in how), None),
                        "left": _data_en(cell(g, il)), "in": clean(cell(g, ii)) or None, "since": _data_en(cell(g, isn))})
        return out
    return []


def stesso(a, b):
    """Stessa persona: nomi uguali senza accenti, oppure stesso cognome."""
    n = lambda s: re.sub(r"[^a-z ]", "", unicodedata.normalize("NFKD", s or "").encode("ascii", "ignore").decode().lower()).split()
    x, y = n(a), n(b)
    return bool(x and y and (x == y or x[-1] == y[-1]))


def allenatore_attuale(ten, cambi):
    """Chi allena adesso: Wikipedia in italiano (giornate in panchina) e in inglese (cambi con le date); vince
    la fonte che conosce il cambio più recente. -> (nome, lasciato): nome è None se la panchina è vuota, e
    lasciato dice chi è andato via, dopo quale giornata, quando e come."""
    r = cambi[-1] if cambi else None
    if ten:
        name, closed = ten[-1]["name"], bool(ten[-1].get("to"))
        if r and stesso(r["out"], name) and not (r["in"] and stesso(r["in"], name)):
            name, closed = (r["in"], False) if r["in"] else (name, True)   # l'inglese sa già dell'addio o del successore
    elif r:
        name, closed = (r["in"], False) if r["in"] else (r["out"], True)
    else:
        return None, None
    if not closed:
        return name, None
    after = ten[-1]["to"] if ten and stesso(ten[-1]["name"], name) else None
    info = next((c for c in reversed(cambi or []) if stesso(c["out"], name)), {})
    return None, {"name": name, "after": after, "date": info.get("left"), "how": info.get("how")}


# ---------- ESPN ----------

def espn_h2h(summary):
    """Ultimi precedenti dal riepilogo ESPN: [(id ESPN di casa, id ESPN in trasferta, gol casa, gol trasferta)]."""
    out = []
    for s in summary.get("seasonseries") or []:
        if s.get("type") != "head-to-head":
            continue
        for e in s.get("events") or []:
            if not (e.get("statusType") or {}).get("completed"):
                continue
            c = {x.get("homeAway"): x for x in e.get("competitors") or []}
            try:
                out.append((str(c["home"]["team"]["id"]), str(c["away"]["team"]["id"]),
                            int(c["home"]["score"]), int(c["away"]["score"])))
            except (KeyError, TypeError, ValueError):
                continue
    return out


def espn_referee(summary):
    for o in (summary.get("gameInfo") or {}).get("officials") or []:
        if ((o.get("position") or {}).get("name") or "").lower() == "referee" and o.get("fullName"):
            return o["fullName"]
    return None


def espn_cards(summary):
    """Cartellini gialli e rossi della partita (somma delle due squadre), se la partita è finita."""
    y = r = 0
    teams = (summary.get("boxscore") or {}).get("teams") or []
    if len(teams) != 2:
        return None
    for t in teams:
        st = {s.get("name"): s.get("displayValue") for s in t.get("statistics") or []}
        if st.get("yellowCards") is None:
            return None
        y += int(float(st.get("yellowCards") or 0))
        r += int(float(st.get("redCards") or 0))
    return {"y": y, "r": r}


def espn_goals(summary):
    """Gol della partita: squadra ESPN, marcatore e assist (id ESPN). Gli autogol sono segnati a parte."""
    out = []
    for k in summary.get("keyEvents") or []:
        if not k.get("scoringPlay"):
            continue
        typ = ((k.get("type") or {}).get("text") or "").lower()
        ps = [str((p.get("athlete") or {}).get("id")) for p in k.get("participants") or [] if (p.get("athlete") or {}).get("id")]
        out.append({"team": str((k.get("team") or {}).get("id")), "g": ps[0] if ps else None,
                    "a": ps[1] if len(ps) > 1 and "own" not in typ else None,
                    "og": "own" in typ, "pen": "penalty" in typ})
    return out


def espn_subs(summary):
    """Sostituzioni in ordine: (squadra ESPN, id entrato, id uscito)."""
    out = []
    for k in summary.get("keyEvents") or []:
        if ((k.get("type") or {}).get("type") or "") != "substitution":
            continue
        ps = [str((p.get("athlete") or {}).get("id")) for p in k.get("participants") or []]
        if len(ps) >= 2:
            out.append((str((k.get("team") or {}).get("id")), ps[0], ps[1]))
    return out

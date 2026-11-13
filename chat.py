"""Chat «Chiedi a Claude»: domande sui dati dell'app, solo sul Mac.
Pezzo di server.py (diviso il 13/11/2026): i nomi restano raggiungibili come server.<nome>. Importare sempre
server, mai questo file da solo."""
import server
from server import (
    DATA_BASE, DATA_DIR, FANTA, HISTORY, LEGA, MATCHES, PRIOR, Path, ROOT, STATE, _r, analysis, asyncio, errtxt,
    json, model, not_ready, os, profiles_out, re, readings, recent_read, recent_rounds, shlex, shutil, subprocess,
    sys, time, unicodedata, web)


# ---------- chat: domande a Claude sui dati dell'app (solo sul Mac) ----------

CHAT_DIR = DATA_DIR / "chat"   # i dati per Claude, in file che può solo leggere e cercare
CHAT = {"key": None, "lock": None, "times": []}
# domande al massimo in un'ora (11/11/2026, revisione del 09/11): la pagina del Mac risponde a chiunque raggiunga la
# porta da questo Mac, e ogni domanda consuma l'abbonamento Claude
CHAT_MAX_HOUR = 30
# il limite vale per tutte le leghe insieme (revisione del 13/11/2026: con un contatore per processo erano 9 x 30):
# orari e id delle sessioni emesse stanno in un file nella cartella comune, protetto da un blocco di sistema
CHAT_STATE = DATA_BASE / "chat-stato.json"


def chat_stato(fn):
    """Legge chat-stato.json, ci applica fn(stato) e lo riscrive, con il file bloccato (fcntl) contro gli altri processi."""
    import fcntl
    DATA_BASE.mkdir(parents=True, exist_ok=True)
    with open(str(CHAT_STATE) + ".lock", "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            st = json.loads(CHAT_STATE.read_text(encoding="utf-8"))
            if not isinstance(st, dict):
                st = {}
        except (OSError, ValueError):
            st = {}
        st["times"] = [t for t in st.get("times", []) if isinstance(t, (int, float)) and time.time() - t < 3600]
        st["sessions"] = [s for s in st.get("sessions", []) if isinstance(s, str)][-500:]
        res = fn(st)
        tmp = CHAT_STATE.with_suffix(".tmp")
        tmp.write_text(json.dumps(st), encoding="utf-8")
        os.replace(str(tmp), str(CHAT_STATE))
        return res


def chat_prenota(now):
    """True se c'è posto tra le domande dell'ultima ora (di tutte le leghe), e la conta."""
    def f(st):
        if len(st["times"]) >= CHAT_MAX_HOUR:
            return False
        st["times"].append(now)
        return True
    return chat_stato(f)


def chat_rimborsa(now):
    """Toglie una domanda che non è arrivata a Claude (non si avvia, risposta illeggibile, login)."""
    def f(st):
        if now in st["times"]:
            st["times"].remove(now)
    chat_stato(f)


def chat_sessione(sid=None):
    """Con sid dice se l'abbiamo emesso noi; senza, niente. Aggiunge sid all'elenco se è nuovo (vedi h_chat)."""
    def f(st):
        return sid in st["sessions"]
    return chat_stato(f)


def chat_registra(sid):
    def f(st):
        if sid not in st["sessions"]:
            st["sessions"].append(sid)
    chat_stato(f)
# al posto delle istruzioni di Claude Code (pensate per programmare): solo queste, così ogni domanda pesa meno
CHAT_PROMPT = """Sei l'assistente di Serie A Live, l'app di statistiche e pronostici dell'utente; qui parli della {league} (stagione {season}).
Oggi è {today}. Rispondi in italiano, in modo chiaro e breve, per una persona che non è un tecnico.
I dati stanno in file JSON nella cartella {folder}. Parti da {folder}/indice.json per sapere cosa c'è, poi usa
Read (con il percorso completo) o Grep solo sui file che servono. Per un giocatore usa Grep su giocatori.jsonl con il
nome in minuscolo e senza accenti (es. "lautaro martinez", o solo il cognome): ogni riga è un giocatore completo.
Prima di dire che un dato manca, riprova la ricerca con una parte del nome. Usa SOLO quei dati: non inventare numeri né
notizie, e se un dato non c'è dillo. Quando dai un numero di' da dove viene (statistiche della stagione,
pronostico dell'app, fonte). Probabilità e dati attesi sono stime del modello dell'app, non certezze. Per le
partite di' se le formazioni sono probabili, stimate o ufficiali. Niente tabelle larghe: elenchi brevi o frasi."""
# domande che chiedono di ragionare (non solo di cercare un dato): per queste il modello più forte
CHAT_DEEP = re.compile(r"perch|convien|consigl|confront|analizz|spieg|schier|meglio|strateg|valut|differenz|rischi", re.I)


def slug(s):
    s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def chat_files():
    """Scrive (quando cambiano i dati) i file che Claude legge per rispondere: indice, classifica, partite,
    pronostici completi della prossima giornata, squadre, giocatori, in evidenza, fanta, storico."""
    an = analysis()
    R = readings()
    ck = (an["key"], R["key"])
    if CHAT["key"] == ck and (CHAT_DIR / "indice.json").exists():
        return
    d, A, pub = STATE["data"], an["A"], an["pub"]
    name = lambda tid: (A["T"].get(str(tid)) or {}).get("team", {}).get("name") or str(tid)
    CHAT_DIR.mkdir(parents=True, exist_ok=True)
    for f in list(CHAT_DIR.glob("*.json")) + list(CHAT_DIR.glob("*.jsonl")):
        f.unlink()
    files = {}

    def put(fname, obj, what):
        (CHAT_DIR / fname).write_text(json.dumps(_r(obj, 3), ensure_ascii=False, indent=1), encoding="utf-8")
        files[fname] = what

    put("classifica.json", [{"pos": r["pos"], "squadra": r["team"]["name"], "punti": r["pts"], "giocate": r["p"], "V": r["w"],
                             "N": r["d"], "P": r["l"], "gol_fatti": r["gf"], "gol_subiti": r["ga"]} for r in d["standings"]["total"]],
        "classifica attuale")
    put("risultati.json", [{"giornata": e.get("round"), "data": time.strftime("%d/%m/%Y", time.localtime(e["start"])),
                            "partita": f"{e['home']['name']} - {e['away']['name']}", "risultato": f"{e['hs']}-{e['as']}"}
                           for e in d.get("played") or [] if e.get("hs") is not None], "risultati delle partite giocate")
    put("calendario.json", [{"giornata": e.get("round"), "data": time.strftime("%d/%m/%Y %H:%M", time.localtime(e["start"])),
                             "partita": f"{e['home']['name']} - {e['away']['name']}",
                             "pronostico": {k: (an["fixtures"].get(str(e["id"])) or {}).get(k) for k in ("p1", "px", "p2", "pick", "lh", "la")}}
                            for e in sorted(d.get("next") or [], key=lambda e: e["start"]) if e.get("status") == "notstarted"][:40],
        "prossime partite con il pronostico sintetico (p1/px/p2 = probabilità di 1, X, 2; lh/la = gol attesi)")
    for e, P in an.get("preds") or []:
        fname = f"partita-{slug(e['home']['name'])}-{slug(e['away']['name'])}.json"
        put(fname, {"partita": f"{e['home']['name']} - {e['away']['name']}", "giornata": e.get("round"),
                    "data": time.strftime("%d/%m/%Y %H:%M", time.localtime(e["start"])), "pronostico": P},
            f"pronostico completo di {e['home']['name']} - {e['away']['name']} (probabilità, gol attesi, formazioni e loro fonte, "
            f"statistiche previste per ogni giocatore, rischio giallo, scontro di stili, arbitro, assenti)")
    teams_players = {}
    for p in d.get("players") or []:
        teams_players.setdefault(str(p.get("teamId")), []).append(p)
    keys = ("minutesPlayed", "appearances", "matchesStarted", "goals", "assists", "expectedGoals", "expectedAssists", "totalShots",
            "shotsOnTarget", "keyPasses", "fouls", "wasFouled", "yellowCards", "redCards", "rating", "fantamedia",
            "tackles", "interceptions", "recoveries", "groundWon", "groundDuels", "aerialWon", "aerialDuels", "progCarries",
            "goalsPrevented", "xgotConceded")
    # un giocatore per riga, con il nome senza accenti in "cerca": una ricerca per nome restituisce subito tutte le sue
    # statistiche, senza leggere il file intero
    rows = [dict({"cerca": slug(p.get("name")).replace("-", " "), "nome": p.get("name"), "squadra": name(p.get("teamId")),
                  "ruolo": p.get("pos")}, **{k: _r(p.get(k), 3) for k in keys if p.get(k) is not None})
            for p in sorted(d.get("players") or [], key=lambda p: -(p.get("minutesPlayed") or 0))]
    (CHAT_DIR / "giocatori.jsonl").write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in rows) + "\n", encoding="utf-8")
    files["giocatori.jsonl"] = ("statistiche della stagione di tutti i giocatori, UNO PER RIGA (ruolo G/D/M/F; rating = media "
                                "voto Fantacalcio.it; fouls = falli fatti, wasFouled = falli subiti; tackles, interceptions, recoveries, duelli "
                                "(groundWon/groundDuels, aerialWon/aerialDuels), progCarries, goalsPrevented, xgotConceded = Opta; "
                                "expectedGoals ed expectedAssists = media di Understat e Opta). Per un giocatore usa Grep "
                                "con il nome in minuscolo e senza accenti (campo cerca), NON leggere il file intero")
    for tid, t in pub["teams"].items():
        put(f"squadra-{slug(name(tid))}.json", {"squadra": name(tid), "analisi": t,
                                                "giocatori": [p.get("name") for p in teams_players.get(tid, [])]},
            f"analisi di {name(tid)}: statistiche e posizione in lega, stile, allenatore, su chi fa affidamento, forma")
    put("in-evidenza.json", an["evidenza"], "giocatori in evidenza della prossima giornata (primi 10 per ogni statistica "
        "prevista, kp = chance create) e, in season, le classifiche della stagione con i dati reali (tot = totale, pg = a "
        "partita, solo con almeno minApps presenze)")
    put("metriche.json", pub["metrics"], "spiegazione delle statistiche di squadra (chiavi usate nei file delle squadre)")
    if FANTA.get("teams"):
        put("fanta.json", model.fanta(an["A"], FANTA, d, MATCHES, server.SQUADS.get("players", {})),
            "le squadre del fantacalcio dell'utente con i punti attesi dei giocatori")
    put("storico.json", {"riepilogo": model.history_summary(HISTORY, model.freq_1x2(PRIOR.get("results"))), "partite": list(HISTORY.get("matches", {}).values())[-40:]},
        "storico dei pronostici dell'app e quanto ci ha azzeccato")
    rr = recent_rounds(R, 3)
    put("letture.json", {"giornate": {str(k): R["rounds"][k] for k in rr},
                         "partite": [dict(r, partita=f"{R['names'].get(r['home'], r['home'])} {r['hs']}-{r['as']} {R['names'].get(r['away'], r['away'])}")
                                     for r in sorted(R["reads"].values(), key=lambda r: -r["start"]) if recent_read(r, rr)]},
        "letture delle ultime giornate: per ogni partita come sono nati i gol (why, lab = perché: errore, palla inattiva, "
        "transizione, seconda palla, difesa superata, prodezza), come hanno giocato le squadre (game), perché il pronostico "
        "è andato così (verdict) e i difetti che si ripetono (lessons); fonti: cronaca Opta di ESPN e tiri di Understat")
    put("profili-squadre.json", {R["names"].get(t, t): v for t, v in profiles_out(R).items()},
        "come segna e come subisce ogni squadra in stagione: gol per tipo (gf fatti, ga subiti: azione, corner, punizione, "
        "contropiede, rigore, autogol), errori individuali, gol nel finale, xG a partita per situazione (xgf/xga)")
    (CHAT_DIR / "indice.json").write_text(json.dumps({"aggiornato": time.strftime("%d/%m/%Y %H:%M"), "file": files},
                                                      ensure_ascii=False, indent=1), encoding="utf-8")
    CHAT["key"] = ck


def claude_bin():
    """Claude Code: quello che si aggiorna da solo (~/.local/bin), altrimenti quello installato con l'app di Claude."""
    local = Path.home() / ".local" / "bin" / "claude"
    if local.exists():
        return str(local)
    found = sorted(Path.home().glob("Library/Application Support/Claude/claude-code/*/claude.app/Contents/MacOS/claude"),
                   key=lambda p: p.stat().st_mtime)
    return str(found[-1]) if found else shutil.which("claude")


def claude_restricted(exe):
    """Se questa versione di Claude Code ha --restricted (confina i file alla cartella di lavoro): si guarda una volta."""
    if exe not in CHAT.setdefault("restricted", {}):
        try:
            r = subprocess.run([exe, "--help"], capture_output=True, text=True, timeout=20)
            CHAT["restricted"][exe] = "--restricted" in (r.stdout + r.stderr)
        except Exception:
            CHAT["restricted"][exe] = False
    return CHAT["restricted"][exe]


async def h_chat(req):
    """Una domanda a Claude: legge solo i file della cartella chat e risponde. Risposte con il tuo account Claude."""
    if not STATE["data"]:
        return not_ready()
    try:   # un corpo non JSON o non oggetto è una richiesta sbagliata, non un errore del server (revisione dell'08/11/2026)
        body = await req.json()
    except ValueError:
        raise web.HTTPBadRequest()
    if not isinstance(body, dict) or not isinstance(body.get("q") or "", str):
        raise web.HTTPBadRequest()
    q = (body.get("q") or "").strip()[:2000]
    if not q:
        raise web.HTTPBadRequest()
    exe = claude_bin()
    if not exe:
        return web.json_response({"error": "Non trovo Claude su questo Mac: serve l'app di Claude."})
    now = time.time()
    if not await asyncio.to_thread(chat_prenota, now):
        return web.json_response({"error": f"Già {CHAT_MAX_HOUR} domande nell'ultima ora: riprova più tardi."})
    CHAT["lock"] = CHAT["lock"] or asyncio.Lock()
    async with CHAT["lock"]:
        # nel ciclo principale, non in un thread: chat_files legge analysis() e STATE, che il ciclo cambia (revisione
        # del 09/11/2026). Dura circa 0,2 secondi e solo quando i dati sono cambiati
        chat_files()
        d = STATE["data"]
        prompt = CHAT_PROMPT.format(league=LEGA["name"], season=(d.get("season") or {}).get("year", ""), today=time.strftime("%d/%m/%Y %H:%M"),
                                    folder=CHAT_DIR)
        model_name = "sonnet" if CHAT_DEEP.search(q) or len(q) > 160 else "haiku"   # difficile se chiede di ragionare o è lunga
        # solo la cartella della chat: Read, Grep e Glob leggerebbero qualsiasi file del Mac con un percorso assoluto.
        # La guardia (chat_guardia.py) blocca ogni percorso fuori dalla cartella; --restricted fa lo stesso dove c'è
        guard = " ".join(shlex.quote(x) for x in (sys.executable, "-I", str(ROOT / "chat_guardia.py"), str(CHAT_DIR)))
        hooks = {"hooks": {"PreToolUse": [{"matcher": "Read|Grep|Glob", "hooks": [{"type": "command", "command": guard}]}]}}
        # la domanda passa da stdin, non come argomento: «--version» o «--dangerously-skip-permissions» scritti come
        # domanda diventavano opzioni di Claude (revisione del 09/11/2026)
        args = [exe, "-p", "--output-format", "json", "--model", model_name, "--tools", "Read,Grep,Glob",
                "--allowedTools", "Read,Grep,Glob", "--system-prompt", prompt, "--strict-mcp-config",
                "--settings", json.dumps(hooks)] + (["--restricted"] if await asyncio.to_thread(claude_restricted, exe) else [])
        sess = body.get("session")
        # solo sessioni nate da questa chat: --resume con un id qualunque riaprirebbe una conversazione di Claude Code
        if isinstance(sess, str) and re.fullmatch(r"[\w-]{8,64}", sess) and await asyncio.to_thread(chat_sessione, sess):
            args += ["--resume", sess]
        proc = None
        try:
            # senza la chiave dell'API nell'ambiente: la chat usa l'abbonamento, non deve poter spendere a consumo
            env = {k: v for k, v in os.environ.items() if k not in ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN")}
            proc = await asyncio.create_subprocess_exec(*args, cwd=str(CHAT_DIR), stdin=asyncio.subprocess.PIPE, env=env,
                                                        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
            out, err = await asyncio.wait_for(proc.communicate(q.encode("utf-8")), timeout=180)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()   # se no il processo resta zombie
            return web.json_response({"error": "Claude non ha risposto entro 3 minuti: riprova con una domanda più precisa."})
        except OSError as ex:
            await asyncio.to_thread(chat_rimborsa, now)
            return web.json_response({"error": f"Claude non si avvia: {errtxt(ex)}"})
    try:
        res = json.loads(out.decode() or "{}")
    except ValueError:
        await asyncio.to_thread(chat_rimborsa, now)
        return web.json_response({"error": (err.decode() or out.decode() or "Risposta non leggibile")[-300:]})
    text = res.get("result") or ""
    if res.get("is_error"):
        await asyncio.to_thread(chat_rimborsa, now)
        if "login" in text.lower() or "logged in" in text.lower():
            return web.json_response({"error": "login", "detail": text})
        return web.json_response({"error": text[:300] or "Errore di Claude"})
    sid = res.get("session_id")
    if isinstance(sid, str) and sid:
        await asyncio.to_thread(chat_registra, sid)
    return web.json_response({"answer": text, "session": sid, "model": model_name})

"""Sito di Serie A Live su GitHub Pages: la versione tascabile.

GitHub Pages fa solo da vetrina, i dati li prende e li calcola l'app. Il sito sta nel ramo "sito" del
repository e lo aggiorna GitHub Actions ogni 15 minuti, anche con il Mac spento (vedi server.py --cloud e
.github/workflows/aggiorna.yml). Il commit è sempre uno solo, sovrascritto ogni volta, così il repository
non cresce. Lo stesso vale per il ramo "dati", da cui riparte ogni aggiornamento.

    python sito.py codice   carica nel ramo main il codice dell'app (da rifare dopo ogni modifica)
    python sito.py dati     carica nel ramo "dati" i dati del Mac, al posto di quelli su GitHub
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ICON = ROOT / "Icona Serie A.png"
# quello che serve a GitHub Actions per aggiornare il sito: va nel ramo main
CODICE = ["server.py", "model.py", "fonti.py", "statistiche.py", "sito.py", "tascabile.html", "Icona Serie A.png",
          "requirements.txt"]
CLOUD_FILES = {"cloud/aggiorna.yml": ".github/workflows/aggiorna.yml", "cloud/README.md": "README.md"}
# i dati da cui riparte ogni aggiornamento su GitHub: vanno nel ramo "dati"
DATI = ["history.json", "fanta.json", "cache/data.json", "cache/squads.json", "cache/prior.json", "cache/matches.json",
        "cache/coaches.json", "cache/espn.json", "cache/fonti.json", "cache/giocatori.json",
        "cache/fantacalcio-statistiche.json", "cache/understat-*.json"]
DATI_IGNORA = "cache/img/\n*.tmp\nfotografia.json\n"

HEAD = """<!doctype html>
<html lang="it"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="robots" content="noindex,nofollow">
<meta name="theme-color" content="#1B7A4B">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Serie A">
<link rel="apple-touch-icon" href="icona-180.png">
<link rel="icon" type="image/png" href="icona-192.png">
<link rel="manifest" href="manifest.webmanifest">
<style>:root{padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}body{margin:0}img{max-width:100%}[hidden]{display:none!important}</style>
</head><body>
"""
TAIL = "\n</body></html>\n"
MANIFEST = {"name": "Serie A Tascabile", "short_name": "Serie A", "start_url": "./", "scope": "./", "display": "standalone",
            "background_color": "#F2F5F0", "theme_color": "#1B7A4B",
            "icons": [{"src": "icona-192.png", "sizes": "192x192", "type": "image/png"},
                      {"src": "icona-512.png", "sizes": "512x512", "type": "image/png"}]}


def firma(snap):
    """Impronta dei dati (senza gli orari di generazione) e della pagina: cambia solo se c'è qualcosa di nuovo."""
    s = {k: v for k, v in snap.items() if k not in ("generatedAt", "statsAt")}
    h = hashlib.sha1(json.dumps(s, sort_keys=True, ensure_ascii=False).encode())
    h.update((ROOT / "tascabile.html").read_bytes())
    return h.hexdigest()


def riduci(src, dst, size, square=False):
    """Immagine ridotta con sips (Mac). Su GitHub sips non c'è: si copia l'originale (serve solo per una squadra nuova)."""
    if shutil.which("sips"):
        size_args = ["-z", str(size), str(size)] if square else ["-s", "format", "png", "-Z", str(size)]
        subprocess.run(["sips", *size_args, str(src), "--out", str(dst)], capture_output=True)
    else:
        shutil.copyfile(src, dst)


def loghi(site, snap, img_dir):
    """Loghi delle squadre (da quelli già scaricati dall'app), ridotti a 96 pixel: restituisce le squadre che ce l'hanno."""
    out_dir = site / "loghi"
    out_dir.mkdir(parents=True, exist_ok=True)
    have = []
    for tid in snap.get("teams") or {}:
        src = next((img_dir / f"team-{tid}.{ext}" for ext in ("png", "webp", "jpg") if (img_dir / f"team-{tid}.{ext}").exists()), None)
        dst = out_dir / f"{tid}.png"
        if src and (not dst.exists() or dst.stat().st_mtime < src.stat().st_mtime):
            riduci(src, dst, 96)
        if dst.exists():
            have.append(str(tid))
    return have


def prepara(site, snap, img_dir=None):
    """Scrive nella cartella del sito la pagina, i dati, l'icona e il manifest (per la schermata Home)."""
    site.mkdir(parents=True, exist_ok=True)
    if img_dir:
        snap = dict(snap, logos=loghi(site, snap, img_dir))
    page = (ROOT / "tascabile.html").read_text().replace("__DATI__", "null")
    page = re.sub(r'\s*<div class="icona">.*?</div>', "", page, count=1, flags=re.S)   # sul sito l'icona c'è già
    (site / "index.html").write_text(HEAD + page + TAIL)
    (site / "dati.json").write_text(json.dumps(snap, ensure_ascii=False))
    (site / "manifest.webmanifest").write_text(json.dumps(MANIFEST, ensure_ascii=False, indent=1))
    (site / ".nojekyll").write_text("")
    (site / "robots.txt").write_text("User-agent: *\nDisallow: /\n")
    for size in (180, 192, 512):
        out = site / f"icona-{size}.png"
        if not out.exists() and ICON.exists():
            riduci(ICON, out, size, square=True)


def git(site, *args, timeout=90):
    env = dict(os.environ, GIT_TERMINAL_PROMPT="0")   # senza credenziali salvate fallisce invece di restare in attesa
    r = subprocess.run(["git", "-C", str(site), *args], capture_output=True, text=True, timeout=timeout, env=env)
    return r.returncode, (r.stdout + r.stderr).strip()


def collega(site, remote):
    """Crea il repository locale (una volta) e lo collega a quello su GitHub."""
    site.mkdir(parents=True, exist_ok=True)
    if not (site / ".git").exists():
        git(site, "init", "-q", "-b", "main")
        git(site, "config", "user.name", "Serie A Live")
        git(site, "config", "user.email", "serie-a-live@users.noreply.github.com")
    code, url = git(site, "remote", "get-url", "origin")
    if code != 0:
        git(site, "remote", "add", "origin", remote)
    elif url != remote:
        git(site, "remote", "set-url", "origin", remote)


def salva(site):
    """Un solo commit con lo stato attuale del sito."""
    git(site, "add", "-A")
    if git(site, "rev-parse", "--verify", "-q", "HEAD")[0] == 0:
        return git(site, "commit", "-q", "--amend", "--no-edit", "--allow-empty")
    return git(site, "commit", "-q", "-m", "Serie A Live")


def pubblica(site, branches=("main",), lease=False):
    """Manda il commit ai rami indicati. Con lease non sovrascrive un ramo cambiato da altri nel frattempo."""
    salva(site)
    code, out = git(site, "push", "-q", "--force-with-lease" if lease else "-f", "origin", *[f"HEAD:{b}" for b in branches])
    return code == 0, out


def pubblica_codice(remote):
    """Copia il codice dell'app nel ramo main del repository, da dove lo prende GitHub Actions."""
    with tempfile.TemporaryDirectory() as tmp:
        dest = Path(tmp) / "codice"
        env = dict(os.environ, GIT_TERMINAL_PROMPT="0")
        r = subprocess.run(["git", "clone", "-q", "--depth", "1", "-b", "main", remote, str(dest)],
                           capture_output=True, text=True, env=env)
        if r.returncode != 0:
            return False, (r.stdout + r.stderr).strip()
        git(dest, "config", "user.name", "Serie A Live")
        git(dest, "config", "user.email", "serie-a-live@users.noreply.github.com")
        git(dest, "rm", "-rq", "--ignore-unmatch", ".")   # nel ramo main ci va solo il codice
        for name in CODICE:
            shutil.copyfile(ROOT / name, dest / name)
        for src, name in CLOUD_FILES.items():
            (dest / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / src, dest / name)
        git(dest, "add", "-A")
        if git(dest, "diff", "--cached", "--quiet")[0] == 0:
            return True, "Il codice su GitHub è già aggiornato"
        git(dest, "commit", "-q", "-m", "Aggiorna il codice di Serie A Live")
        code, out = git(dest, "push", "-q", "origin", "HEAD:main")
        return code == 0, out or "Codice caricato su GitHub"


def pubblica_dati(data_dir, remote):
    """Carica nel ramo "dati" i dati del Mac, sovrascrivendo quelli su GitHub (per partire o ripartire da capo)."""
    with tempfile.TemporaryDirectory() as tmp:
        dest = Path(tmp) / "dati"
        dest.mkdir()
        for pattern in DATI:
            for src in sorted(data_dir.glob(pattern)):
                out = dest / src.relative_to(data_dir)
                out.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, out)
        extra = dest / "cache" / "fonti.json"
        if extra.exists():   # al primo giro su GitHub si riscarica e si ripubblica tutto: si vede subito se qualcosa non va
            e = json.loads(extra.read_text())
            for k in ("usAt", "wikiAt", "rosterAt", "siteAt", "siteSig"):
                e.pop(k, None)
            extra.write_text(json.dumps(e, ensure_ascii=False))
        fanta = dest / "fanta.json"
        if fanta.exists():   # il repository è pubblico: niente soprannomi dei fantallenatori né crediti
            f = json.loads(fanta.read_text())
            for t in f.get("teams") or []:
                t.pop("manager", None)
                t.pop("credits", None)
            fanta.write_text(json.dumps(f, ensure_ascii=False))
        (dest / ".gitignore").write_text(DATI_IGNORA)
        git(dest, "init", "-q", "-b", "dati")
        git(dest, "config", "user.name", "Serie A Live")
        git(dest, "config", "user.email", "serie-a-live@users.noreply.github.com")
        git(dest, "remote", "add", "origin", remote)
        salva(dest)
        code, out = git(dest, "push", "-q", "-f", "origin", "HEAD:dati")
        return code == 0, out or "Dati caricati su GitHub"


if __name__ == "__main__":
    data_dir = Path(os.environ.get("SERIEA_DATA_DIR") or Path.home() / "Library" / "Application Support" / "Serie A Live")
    remote = json.loads((data_dir / "sito.json").read_text())["remote"]
    if sys.argv[1:] == ["codice"]:
        ok, msg = pubblica_codice(remote)
    elif sys.argv[1:] == ["dati"]:
        ok, msg = pubblica_dati(data_dir, remote)
    else:
        ok, msg = False, __doc__
    print(msg)
    sys.exit(0 if ok else 1)

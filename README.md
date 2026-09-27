# Serie A Live

Sito: https://pier21q.github.io/Serie-A/

Il sito si aggiorna da solo sui computer di GitHub (GitHub Actions), anche con il Mac spento. Ogni 15 minuti
l'app scarica le novità da ESPN, Understat, Fantacalcio.it e Wikipedia, ricalcola statistiche e pronostici
e, se è cambiato qualcosa, ripubblica il sito. Durante le partite resta accesa e aggiorna di continuo.

Rami del repository:

- `main`: il codice dell'app e la programmazione (`.github/workflows/aggiorna.yml`)
- `dati`: i dati da cui riparte ogni aggiornamento (un solo commit, sovrascritto ogni volta)
- `sito`: il sito pubblicato da GitHub Pages (un solo commit, sovrascritto ogni volta)
- `storico`: una copia al giorno dello storico dei pronostici, con tutte le versioni (serve a recuperarlo se si rovina)

Per aggiornare subito: Actions → Aggiorna Serie A Live → Run workflow.
Com'è andato l'ultimo aggiornamento: `esecuzione.json` nel ramo `dati`.

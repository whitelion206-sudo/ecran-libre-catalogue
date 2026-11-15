"""Robot du catalogue Écran Libre.

Une fois par jour, il récupère les vidéos des chaînes listées dans chaines.json,
garde seulement les films utilisables par l'appli, et écrit catalogue.json.

Un film est gardé s'il :
- dure au moins DUREE_MIN_MINUTES minutes ;
- est public et peut être intégré dans une autre appli ;
- est autorisé en France ;
- n'est pas réservé aux adultes (ces vidéos ne se lisent pas hors de YouTube) ;
- n'a pas « VOSTFR », « bande-annonce »… dans son titre (VF uniquement) ;
- n'est pas dans exclus.txt.

Les genres viennent du titre YouTube (ce qui suit « Film Complet en Français | »),
complétés par le genre de la chaîne (sauf « Animation », voir fiche_film).

La clé API est lue dans la variable d'environnement YOUTUBE_API_KEY
(un « secret » GitHub), jamais écrite dans ce fichier.
"""

import difflib
import json
import os
import re
import sys
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone

API = "https://www.googleapis.com/youtube/v3/"
PAYS = "FR"
DUREE_MIN_MINUTES = 60

DOSSIER = os.path.dirname(os.path.abspath(__file__))
FICHIER_CHAINES = os.path.join(DOSSIER, "chaines.json")
FICHIER_EXCLUS = os.path.join(DOSSIER, "exclus.txt")
FICHIER_CATALOGUE = os.path.join(DOSSIER, "catalogue.json")


def appel_api(methode, parametres, cle):
    """Appelle l'API YouTube et renvoie la réponse JSON."""
    parametres = dict(parametres, key=cle)
    url = API + methode + "?" + urllib.parse.urlencode(parametres)
    try:
        with urllib.request.urlopen(url, timeout=30) as reponse:
            return json.load(reponse)
    except urllib.error.HTTPError as erreur:
        detail = erreur.read().decode("utf-8", "replace")
        sys.exit(f"Erreur de l'API YouTube ({erreur.code}) sur {methode} : {detail}")


def duree_en_minutes(iso):
    """Convertit une durée YouTube (ex. PT1H26M39S) en minutes."""
    m = re.fullmatch(r"P(?:(\d+)D)?T?(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?", iso or "")
    if not m:
        return 0
    jours, heures, minutes, secondes = (int(x) if x else 0 for x in m.groups())
    return jours * 1440 + heures * 60 + minutes + round(secondes / 60)


def titre_propre(titre):
    """Enlève la fin du type « | Film Complet en Français » ou « - Film COMPLET en VF »."""
    morceau = re.split(r"\s*[|\-–—]\s*(?:film|films)\s+complet", titre, flags=re.IGNORECASE)[0]
    morceau = morceau.split(" | ")[0]
    return morceau.strip(" |-–—") or titre.strip()


MOTS_INTERDITS = re.compile(
    r"\bvost(?:fr)?\b|\bvo\b|version originale|sous[- ]titr|bande[- ]annonce|\btrailer\b|\bteaser\b",
    flags=re.IGNORECASE,
)

GENRES_CONNUS = [
    "Action", "Animation", "Arts martiaux", "Aventure", "Biopic", "Catastrophe",
    "Comédie", "Comédie dramatique", "Comédie romantique", "Crime", "Documentaire", "Drame", "Famille",
    "Fantastique", "Guerre", "Historique", "Horreur", "Musical", "Mystère", "Noël",
    "Policier", "Romance", "Science-fiction", "Sport", "Thriller", "Western",
]

GENRES_RENOMMES = {
    "teen": "Ados",
    "teen movie": "Ados",
    "fantasy": "Fantastique",
    "suspense": "Thriller",
    "sci-fi": "Science-fiction",
    "science fiction": "Science-fiction",
    "epouvante": "Horreur",
    "aventures": "Aventure",
    "comedy": "Comédie",
    "drama": "Drame",
    "horror": "Horreur",
}


def sans_accents(texte):
    return unicodedata.normalize("NFKD", texte).encode("ascii", "ignore").decode().lower()


def genre_normalise(genre):
    """Corrige les fautes et variantes (« Thriler », « Comedie »…) vers un nom unique."""
    cle = sans_accents(genre)
    if cle in GENRES_RENOMMES:
        return GENRES_RENOMMES[cle]
    connus = {sans_accents(g): g for g in GENRES_CONNUS}
    proche = difflib.get_close_matches(cle, connus, n=1, cutoff=0.9)
    if proche:
        return connus[proche[0]]
    # « Thriller psychologique » -> « Thriller », « Film d'action » -> « Action »
    contenus = [k for k in connus if re.search(r"\b" + re.escape(k) + r"\b", cle)]
    if contenus:
        return connus[max(contenus, key=len)]
    for k, nom in GENRES_RENOMMES.items():
        if re.search(r"\b" + re.escape(k) + r"\b", cle):
            return nom
    return genre[0].upper() + genre[1:].lower()


def genres_du_titre(titre):
    """Lit les genres écrits après « Film Complet en Français | » dans le titre YouTube."""
    morceaux = [m.strip() for m in titre.split("|")]
    for i, morceau in enumerate(morceaux):
        if re.search(r"films?\s+complets?", morceau, flags=re.IGNORECASE) and i + 1 < len(morceaux):
            genres = []
            for genre in re.split(r"[,/]", morceaux[i + 1]):
                genre = genre.strip()
                if not genre:
                    continue
                genre = genre_normalise(genre)
                if genre not in genres:
                    genres.append(genre)
            return genres
    return []


def autorise_en_france(details):
    restriction = details.get("contentDetails", {}).get("regionRestriction", {})
    if "allowed" in restriction and PAYS not in restriction["allowed"]:
        return False
    if PAYS in restriction.get("blocked", []):
        return False
    return True


def est_utilisable(video, exclus):
    statut = video.get("status", {})
    contenu = video.get("contentDetails", {})
    if video["id"] in exclus:
        return False
    if MOTS_INTERDITS.search(video.get("snippet", {}).get("title", "")):
        return False
    if statut.get("privacyStatus") != "public" or not statut.get("embeddable", False):
        return False
    if contenu.get("contentRating", {}).get("ytRating") == "ytAgeRestricted":
        return False
    if duree_en_minutes(contenu.get("duration")) < DUREE_MIN_MINUTES:
        return False
    return autorise_en_france(video)


def miniature(snippet):
    vignettes = snippet.get("thumbnails", {})
    for taille in ("maxres", "standard", "high", "medium", "default"):
        if taille in vignettes:
            return vignettes[taille]["url"]
    return ""


def videos_de_la_chaine(id_chaine, cle):
    """Renvoie les identifiants de toutes les vidéos mises en ligne par la chaîne."""
    reponse = appel_api("channels", {"part": "contentDetails", "id": id_chaine}, cle)
    if not reponse.get("items"):
        print(f"Chaîne introuvable : {id_chaine}")
        return []
    liste = reponse["items"][0]["contentDetails"]["relatedPlaylists"]["uploads"]
    ids, page = [], None
    while True:
        parametres = {"part": "contentDetails", "playlistId": liste, "maxResults": 50}
        if page:
            parametres["pageToken"] = page
        reponse = appel_api("playlistItems", parametres, cle)
        ids += [item["contentDetails"]["videoId"] for item in reponse.get("items", [])]
        page = reponse.get("nextPageToken")
        if not page:
            return ids


def details_des_videos(ids, cle):
    details = []
    for debut in range(0, len(ids), 50):
        paquet = ids[debut:debut + 50]
        reponse = appel_api(
            "videos",
            {"part": "snippet,contentDetails,status", "id": ",".join(paquet)},
            cle,
        )
        details += reponse.get("items", [])
    return details


def fiche_film(video, chaine):
    snippet = video["snippet"]
    # Les genres du titre sont les plus précis. Le genre de la chaîne est ajouté
    # en plus, sauf « Animation » : la chaîne Animation publie aussi des films
    # avec de vrais acteurs (ex. « Le Monstre des Sables »).
    genres = genres_du_titre(snippet.get("title", ""))
    genre_chaine = chaine.get("genre", "")
    if genre_chaine and genre_chaine not in genres:
        if not genres:
            genres.append(genre_chaine)
        elif genre_chaine != "Animation":
            genres.append(genre_chaine)
    return {
        "id": video["id"],
        "titre": titre_propre(snippet.get("title", "")),
        "titre_youtube": snippet.get("title", ""),
        "description": snippet.get("description", "")[:500],
        "duree_minutes": duree_en_minutes(video["contentDetails"].get("duration")),
        "date": snippet.get("publishedAt", ""),
        "miniature": miniature(snippet),
        "genre": genres[0] if genres else "",
        "genres": genres,
        "chaine": chaine["nom"],
    }


def lire_exclus():
    if not os.path.exists(FICHIER_EXCLUS):
        return set()
    with open(FICHIER_EXCLUS, encoding="utf-8") as f:
        lignes = (ligne.split("#")[0].strip() for ligne in f)
        return {ligne for ligne in lignes if ligne}


def main():
    cle = os.environ.get("YOUTUBE_API_KEY")
    if not cle:
        sys.exit("Il manque le secret YOUTUBE_API_KEY.")
    with open(FICHIER_CHAINES, encoding="utf-8") as f:
        chaines = json.load(f)
    exclus = lire_exclus()

    films = {}
    for chaine in chaines:
        ids = videos_de_la_chaine(chaine["id"], cle)
        gardes = 0
        for video in details_des_videos(ids, cle):
            if not est_utilisable(video, exclus):
                continue
            fiche = fiche_film(video, chaine)
            deja = films.get(video["id"])
            if deja is None or (not deja["genre"] and fiche["genre"]):
                films[video["id"]] = fiche
            gardes += 1
        print(f"{chaine['nom']} : {len(ids)} vidéos, {gardes} films gardés")

    catalogue = {
        "mis_a_jour": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "nombre_de_films": len(films),
        "films": sorted(films.values(), key=lambda film: film["date"], reverse=True),
    }
    with open(FICHIER_CATALOGUE, "w", encoding="utf-8") as f:
        json.dump(catalogue, f, ensure_ascii=False, indent=1)
    print(f"Catalogue écrit : {len(films)} films.")


if __name__ == "__main__":
    main()

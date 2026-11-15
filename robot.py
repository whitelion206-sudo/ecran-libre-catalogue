"""Robot du catalogue Écran Libre.

Une fois par jour, il récupère les vidéos des chaînes listées dans chaines.json,
garde seulement les films utilisables par l'appli, et écrit catalogue.json.

Un film est gardé s'il :
- dure au moins DUREE_MIN_MINUTES minutes ;
- est public et peut être intégré dans une autre appli ;
- est autorisé en France ;
- n'est pas réservé aux adultes (ces vidéos ne se lisent pas hors de YouTube) ;
- n'a pas « VOSTFR », « bande-annonce »… dans son titre (VF uniquement) ;
- n'est pas dans exclus.txt ;
- pour les chaînes marquées « vf_seulement », a un titre qui dit qu'il est en français.

Les genres viennent du titre YouTube (ce qui suit « Film Complet en Français | »),
complétés par le genre de la chaîne (sauf « Animation », voir fiche_film).

Il ajoute aussi les « classiques » du domaine public listés dans classiques.json,
hébergés sur Wikimedia Commons (réutilisation commerciale permise).

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
FICHIER_CLASSIQUES = os.path.join(DOSSIER, "classiques.json")


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

# Pour les chaînes qui mélangent français et anglais (option "vf_seulement"
# dans chaines.json) : on ne garde que les vidéos dont le titre dit qu'elles
# sont en français.
SIGNES_ANGLAIS = re.compile(
    r"full[\s-]+(?:length\s+)?movie|\benglish\b|free\s+movie",
    flags=re.IGNORECASE,
)
SIGNES_FRANCAIS = re.compile(
    r"fran[cç]ais|\bVF\b|films?\s+complets?|version\s+fran[cç]aise",
    flags=re.IGNORECASE,
)


def est_en_francais(video):
    """Vrai si la vidéo est clairement en français (titre ou langue indiquée)."""
    snippet = video.get("snippet", {})
    titre = snippet.get("title", "")
    if SIGNES_ANGLAIS.search(titre):
        return False
    if SIGNES_FRANCAIS.search(titre):
        return True
    if re.search(r"\bmovie\b", titre, flags=re.IGNORECASE):
        return False
    audio = (snippet.get("defaultAudioLanguage") or "").lower()
    langue = (snippet.get("defaultLanguage") or "").lower()
    return audio.startswith("fr") and langue.startswith("fr")


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


# --- Classiques du domaine public (Wikimedia Commons) -----------------------

COMMONS_API = "https://commons.wikimedia.org/w/api.php"
# Wikimedia demande que chaque robot se présente avec un nom et un contact.
USER_AGENT = "EcranLibreBot/1.0 (https://github.com/whitelion206-sudo/ecran-libre-catalogue)"


def sans_html(texte):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", texte or "")).strip()


def infos_commons(fichiers):
    """Demande à Commons les adresses, la durée, l'image et la licence de chaque fichier."""
    infos = {}
    for debut in range(0, len(fichiers), 50):
        paquet = fichiers[debut:debut + 50]
        parametres = {
            "action": "query",
            "format": "json",
            "formatversion": "2",
            "prop": "videoinfo",
            "viprop": "url|size|mime|derivatives|extmetadata",
            "viurlwidth": "640",
            "titles": "|".join("File:" + f for f in paquet),
        }
        requete = urllib.request.Request(
            COMMONS_API + "?" + urllib.parse.urlencode(parametres),
            headers={"User-Agent": USER_AGENT},
        )
        with urllib.request.urlopen(requete, timeout=60) as reponse:
            donnees = json.load(reponse)
        requete_q = donnees.get("query", {})
        # Commons peut réécrire un nom (ex. « _ » en espace) : on garde la correspondance.
        renomme = {n["to"]: n["from"] for n in requete_q.get("normalized", [])}
        for page in requete_q.get("pages", []):
            nom = renomme.get(page["title"], page["title"])
            nom = nom[len("File:"):] if nom.startswith("File:") else nom
            if page.get("missing") or not page.get("videoinfo"):
                print(f"Classique introuvable sur Commons : {nom}")
                continue
            infos[nom.replace("_", " ")] = page["videoinfo"][0]
    return infos


def choisir_video(info):
    """Choisit une version légère pour le téléphone (environ 480p), et une de secours."""
    versions = []
    for d in info.get("derivatives", []):
        # Seules les versions réencodées par Commons (« /transcoded/ ») sont légères.
        if "webm" not in d.get("type", "") or "/transcoded/" not in d.get("src", ""):
            continue
        versions.append((int(d.get("height") or 0), "vp9" in d.get("type", ""), d["src"]))
    if not versions:
        return info.get("url", ""), info.get("url", "")
    moyennes = [v for v in versions if 300 <= v[0] <= 480]
    principale = max(moyennes or versions, key=lambda v: (v[1], v[0]))
    secours = [v for v in versions if not v[1]] or versions
    return principale[2], min(secours, key=lambda v: v[0])[2]


def fiche_classique(entree, info):
    meta = info.get("extmetadata", {})
    video, video_secours = choisir_video(info)
    duree = info.get("duration")
    return {
        "id": "commons:" + entree["fichier"],
        "titre": entree["titre"],
        "annee": entree.get("annee"),
        "realisation": entree.get("realisation", ""),
        "genre": entree.get("genre", ""),
        "genres": [entree["genre"]] if entree.get("genre") else [],
        "description": entree.get("description", ""),
        "texte_a_l_ecran": entree.get("texte_a_l_ecran", ""),
        "duree_minutes": max(1, round(duree / 60)) if duree else None,
        "video": video,
        "video_secours": video_secours,
        "miniature": info.get("thumburl", ""),
        "licence": sans_html(meta.get("LicenseShortName", {}).get("value", "")),
        "credit": sans_html(meta.get("Artist", {}).get("value", "")),
        "page_source": info.get("descriptionurl", ""),
        "source": "Wikimedia Commons",
    }


def classiques(ancien_catalogue):
    """Construit la liste des classiques. En cas de panne de Commons, garde l'ancienne liste."""
    if not os.path.exists(FICHIER_CLASSIQUES):
        return []
    with open(FICHIER_CLASSIQUES, encoding="utf-8") as f:
        entrees = json.load(f)
    try:
        infos = infos_commons([e["fichier"] for e in entrees])
    except Exception as erreur:  # Commons en panne : on ne casse pas le catalogue YouTube
        print(f"Commons indisponible ({erreur}) : je garde les classiques d'hier.")
        return ancien_catalogue.get("classiques", [])
    liste = []
    for entree in entrees:
        info = infos.get(entree["fichier"].replace("_", " "))
        if info:
            liste.append(fiche_classique(entree, info))
    print(f"Classiques : {len(liste)} sur {len(entrees)} trouvés sur Commons.")
    return liste


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
            if chaine.get("vf_seulement") and not est_en_francais(video):
                continue
            fiche = fiche_film(video, chaine)
            deja = films.get(video["id"])
            if deja is None or (not deja["genre"] and fiche["genre"]):
                films[video["id"]] = fiche
            gardes += 1
        print(f"{chaine['nom']} : {len(ids)} vidéos, {gardes} films gardés")

    ancien = {}
    if os.path.exists(FICHIER_CATALOGUE):
        try:
            with open(FICHIER_CATALOGUE, encoding="utf-8") as f:
                ancien = json.load(f)
        except ValueError:
            ancien = {}

    liste_classiques = classiques(ancien)
    catalogue = {
        "mis_a_jour": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "nombre_de_films": len(films),
        "films": sorted(films.values(), key=lambda film: film["date"], reverse=True),
        "nombre_de_classiques": len(liste_classiques),
        "classiques": liste_classiques,
    }
    with open(FICHIER_CATALOGUE, "w", encoding="utf-8") as f:
        json.dump(catalogue, f, ensure_ascii=False, indent=1)
    print(f"Catalogue écrit : {len(films)} films YouTube et {len(liste_classiques)} classiques.")


if __name__ == "__main__":
    main()

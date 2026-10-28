#!/usr/bin/env python3
"""
House finder: 4-bed rentals in Chiswick, Acton and Gunnersbury/Brentford.
 
One run does everything:
  1. Loads listings from the sources that allow programmatic access
       - listings.json (listings you paste in from any site). Required: name, url,
         postcode, price. Everything else is optional, including a status such as
         Enquired / Viewed / Offer made / Denied
       - PropertyData API (optional, paid with a 14-day free trial): asking-rent
         comparables for 4-beds in each area, and the national HMO licence register
  2. Filters to 4+ bedrooms in the target postcode districts (W3, W4, TW8)
  3. Flags HMO: your own column, keyword match, or a match on the HMO register
  4. Works out drive time to Cody Technology Park (Farnborough) and public
     transport time to 4 More London Place (SE1 2AU) for every listing
  5. Works out both commutes across a grid from London to Farnborough and shades
     the map where they are under 45 / 60 / 75 / 90 minutes (commute hotspots)
  6. Writes an interactive map (house_map.html), pins coloured by status, and a
     table (results.csv)
 
Usage:
    pip install requests folium
    python house_finder.py --open           # uses listings.json next to this file
    python house_finder.py --listings other.json --min-beds 4
 
Optional environment variables:
    PROPERTYDATA_API_KEY   turns on the PropertyData comparables + HMO register
    TFL_APP_KEY            TfL API key (free); works without one at low volume
    GOOGLE_MAPS_API_KEY    Google Maps Routes API key: traffic-aware drive times and
                           transit times for 8am, with a best-to-worst range
    ORS_API_KEY            OpenRouteService key (free); used for driving if there is
                           no Google key, otherwise the public OSRM server is used
 
Rightmove, Zoopla, OnTheMarket, OpenRent and SpareRoom do not offer a public
listings API and their terms forbid scraping, so this script does not scrape them.
"""
 
import argparse
import csv
import datetime as dt
import html
import json
import math
import os
import re
import sys
import time
import webbrowser
from pathlib import Path
 
try:
    import requests
    import folium
    from folium.plugins import MarkerCluster
except ImportError:
    sys.exit("Missing packages. Run:  pip install requests folium")
 
 
# ---------------------------------------------------------------- settings --
 
HERE = Path(__file__).resolve().parent
CACHE_FILE = HERE / ".house_finder_cache.json"
 
MIN_BEDS = 4
 
# Postcode districts that cover the three areas. Gunnersbury straddles W4 and TW8.
AREAS = {
    # "W4": ("Chiswick / Gunnersbury", 51.4925, -0.2633),
    # "W3": ("Acton", 51.5085, -0.2700),
    # "TW8": ("Brentford / Gunnersbury", 51.4860, -0.3080),
}
 
DESTINATIONS = {
    "cody": {
        "name": "Cody Technology Park, Farnborough",
        "postcode": "GU14 0LX",
        "lat": 51.2810, "lon": -0.7770,      # fallback if the postcode lookup fails
    },
    "london": {
        "name": "4 More London Place, SE1",
        "short": "More London",
        "postcode": "SE1 2AU",
        "lat": 51.5049, "lon": -0.0790,      # fallback if the postcode lookup fails
    },
}
 
# Commute assumptions for the public transport times
COMMUTE_DEPART = "08:00"                     # leave home at 08:00 on the next weekday
TRANSIT_SPREAD_MIN = (-15, 0, 15)            # Google transit range: leave 07:45, 08:00, 08:15
# Without a Google key, driving uses an empty-road time multiplied by these
# (best case, typical, worst case) to allow for the morning rush on the M4/M25/M3.
RUSH_HOUR_FACTORS = (1.15, 1.35, 1.75)
 
# Commute hotspot grid: squares of GRID_KM across this box (south-west, north-east),
# which covers Ealing, Acton, Chiswick, Gunnersbury and Brentford (Kew Bridge to
# North Acton, Hanwell side of West Ealing to Turnham Green).
# Results are saved in commute_grid.json.
GRID_BOUNDS = ((51.470, -0.335), (51.530, -0.235))
GRID_KM = 0.5
# Colour bands for the grid, in minutes (narrow, so differences across a few streets
# show up). Squares over the last limit are not drawn.
GRID_BANDS = [
    (50, "#006837", "under 50"),
    (55, "#1a9850", "50–55"),
    (60, "#66bd63", "55–60"),
    (65, "#d9ef8b", "60–65"),
    (70, "#fee08b", "65–70"),
    (80, "#fdae61", "70–80"),
    (90, "#f46d43", "80–90"),
]
 
HMO_KEYWORDS = re.compile(
    r"\bhmo\b|house in multiple occupation|licen[sc]ed for \d|sharers?\b|"
    r"house share|professional share|students? welcome",
    re.I,
)
 
HTTP = requests.Session()
HTTP.headers["User-Agent"] = "house-finder-script/1.0 (personal use)"
 
 
# ------------------------------------------------------------------- cache --
 
def load_cache():
    try:
        return json.loads(CACHE_FILE.read_text())
    except Exception:
        return {}
 
 
def save_cache(cache):
    try:
        CACHE_FILE.write_text(json.dumps(cache, indent=1))
    except Exception as e:
        print(f"  (could not write cache: {e})")
 
 
CACHE = load_cache()
 
 
def get_json(url, params=None, headers=None, timeout=30, cache_key=None):
    if cache_key and cache_key in CACHE:
        return CACHE[cache_key]
    last = RuntimeError(f"Rate limited by {url}")
    for attempt in range(3):
        try:
            r = HTTP.get(url, params=params, headers=headers, timeout=timeout)
            if r.status_code == 429:
                time.sleep(5 * (attempt + 1))
                continue
            r.raise_for_status()
            data = r.json()
            if cache_key:
                CACHE[cache_key] = data
            return data
        except requests.RequestException as e:
            last = e
            time.sleep(2 * (attempt + 1))
    raise last
 
 
# --------------------------------------------------------------- helpers --
 
def norm_postcode(pc):
    pc = re.sub(r"\s+", "", (pc or "").upper())
    return f"{pc[:-3]} {pc[-3:]}" if len(pc) >= 5 else pc
 
 
def district(pc):
    pc = norm_postcode(pc)
    return pc.split(" ")[0] if " " in pc else pc
 
 
def find_postcode(text):
    m = re.search(r"\b([A-Z]{1,2}\d[A-Z\d]?)\s*(\d[A-Z]{2})\b", (text or "").upper())
    return f"{m.group(1)} {m.group(2)}" if m else ""
 
 
def to_float(v):
    try:
        return float(re.sub(r"[^\d.-]", "", str(v)))
    except (TypeError, ValueError):
        return None
 
 
def to_int(v):
    f = to_float(v)
    return int(f) if f is not None else None
 
 
def yes(v):
    return str(v).strip().lower() in {"y", "yes", "true", "1", "licensed", "hmo"}
 
 
def first_list_of_dicts(obj):
    """PropertyData nests result lists under varying keys; find the first one."""
    if isinstance(obj, list) and obj and isinstance(obj[0], dict):
        return obj
    if isinstance(obj, dict):
        for v in obj.values():
            found = first_list_of_dicts(v)
            if found:
                return found
    return []
 
 
def pick(d, *keys):
    for k in keys:
        if d.get(k) not in (None, ""):
            return d[k]
    return None
 
 
# --------------------------------------------------------------- geocoding --
 
def geocode_postcodes(postcodes):
    """postcodes.io bulk lookup (free, open data). Returns {postcode: (lat, lon)}."""
    out, todo = {}, []
    for pc in {norm_postcode(p) for p in postcodes if p}:
        key = f"pc:{pc}"
        if key in CACHE:
            if CACHE[key]:
                out[pc] = tuple(CACHE[key])
        else:
            todo.append(pc)
    for i in range(0, len(todo), 100):
        chunk = todo[i:i + 100]
        try:
            r = HTTP.post("https://api.postcodes.io/postcodes",
                          json={"postcodes": chunk}, timeout=30)
            r.raise_for_status()
            for item in r.json().get("result", []):
                pc = norm_postcode(item["query"])
                res = item.get("result")
                CACHE[f"pc:{pc}"] = [res["latitude"], res["longitude"]] if res else None
                if res:
                    out[pc] = (res["latitude"], res["longitude"])
        except requests.RequestException as e:
            print(f"  postcodes.io lookup failed: {e}")
    return out
 
 
def geocode_address(address):
    """Nominatim fallback for listings with no postcode (1 request per second)."""
    key = f"addr:{address.lower()}"
    if key in CACHE:
        return tuple(CACHE[key]) if CACHE[key] else None
    time.sleep(1.1)
    try:
        r = HTTP.get("https://nominatim.openstreetmap.org/search",
                     params={"q": address, "format": "json", "limit": 1,
                             "countrycodes": "gb"}, timeout=30)
        r.raise_for_status()
        hits = r.json()
        CACHE[key] = [float(hits[0]["lat"]), float(hits[0]["lon"])] if hits else None
    except requests.RequestException as e:
        print(f"  Nominatim lookup failed for '{address}': {e}")
        return None
    return tuple(CACHE[key]) if CACHE[key] else None
 
 
# ----------------------------------------------------------------- sources --
 
# Status values you can put in listings.json, and the pin colour for each.
# The first word in each tuple is what appears on the map; the rest are accepted spellings.
STATUSES = [
    # (label,             pin colour,  legend hex, accepted spellings)
    ("Not contacted",     "blue",      "#38aadd", {"", "new", "interested", "not contacted", "shortlist", "shortlisted"}),
    ("Enquired",          "purple",    "#d252b9", {"enquired", "enquiry", "contacted", "messaged", "emailed", "called"}),
    ("Viewing booked",    "orange",    "#f69730", {"viewing booked", "viewing", "booked", "viewing arranged"}),
    ("Viewed",            "beige",     "#ffcb92", {"viewed", "seen"}),
    ("Offer made",        "green",     "#72b026", {"offered", "offer", "offer made", "applied", "application"}),
    ("Secured",           "darkgreen", "#728224", {"secured", "accepted", "signed", "holding deposit paid", "won"}),
    ("Denied",            "red",       "#d63e2a", {"denied", "declined", "refused", "rejected by landlord", "unsuccessful"}),
    ("Not for us",        "gray",      "#575757", {"not for us", "rejected", "passed", "no", "not interested"}),
    ("No longer available", "black",   "#303030", {"let", "let agreed", "gone", "unavailable", "withdrawn", "no longer available"}),
]
STATUS_ORDER = {label: i for i, (label, *_ ) in enumerate(STATUSES)}
 
 
def normalise_status(value):
    v = re.sub(r"\s+", " ", str(value or "").strip().lower())
    for label, _, _, spellings in STATUSES:
        if v in spellings or v == label.lower():
            return label
    print(f"  Unknown status '{value}', showing it as 'Not contacted'. "
          f"Use one of: {', '.join(l for l, *_ in STATUSES)}")
    return "Not contacted"
 
 
REQUIRED_FIELDS = {
    "name": "Short name, e.g. '4 bed terrace, Fishers Lane'",
    "url": "Link to the advert",
    "postcode": "Full postcode, e.g. 'W4 1RX'",
    "price": "Rent per month in pounds, e.g. 3800",
}
 
OPTIONAL_FIELDS = {
    "status": "One of: " + ", ".join(l for l, *_ in STATUSES) + ". Blank = Not contacted",
    "notes": "Anything else",
    "bedrooms": "Number, e.g. 4",
    "bathrooms": "Number, e.g. 2",
    "address": "Street address",
    "property_type": "house / flat / maisonette ...",
    "hmo_licensed": "true, false, or null if you don't know",
    "status_date": "When the status last changed, e.g. '2026-10-28'",
    "viewing_date": "e.g. '2026-11-02 18:30'",
    "agent": "Agent or landlord name / phone / email",
    "source": "Where you found it, e.g. Rightmove",
    "available_from": "e.g. '2026-12-01'",
    "lat": "Latitude, only if the postcode puts the pin in the wrong place",
    "lon": "Longitude, as above",
}
 
# Older field names that still work
ALIASES = {"name": ("title",), "price": ("rent_pcm", "rent")}
 
 
def field(row, name):
    for key in (name, *ALIASES.get(name, ())):
        if row.get(key) not in (None, ""):
            return row[key]
    return None
 
 
def write_json_template(path):
    template = {
        "_help": {
            "how": "Add one entry per property to 'listings', separated by commas. Copy the "
                   "blank entry at the bottom. Entries with \"_example\": true are ignored.",
            "required": REQUIRED_FIELDS,
            "optional (leave out, or set to null, if you don't know)": OPTIONAL_FIELDS,
        },
        "listings": [
            {
                "_example": True,
                "name": "4 bed terrace, Fishers Lane",
                "url": "https://www.rightmove.co.uk/properties/000000000",
                "postcode": "W4 1RX",
                "price": 3800,
                "status": "Viewing booked",
                "viewing_date": "2026-11-02 18:30",
                "bedrooms": 4,
                "notes": "Sharers welcome",
            },
            {"name": "", "url": "", "postcode": "", "price": None, "status": "", "notes": ""},
        ],
    }
    path.write_text(json.dumps(template, indent=2) + "\n")
 
 
def read_rows(path):
    """Rows from listings.json (or a .csv with the same column names)."""
    if path.suffix.lower() == ".csv":
        with open(path, newline="", encoding="utf-8-sig") as f:
            return [{(k or "").strip().lower(): v for k, v in r.items()} for r in csv.DictReader(f)]
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    rows = data.get("listings", []) if isinstance(data, dict) else data
    return [r for r in rows if isinstance(r, dict)]
 
 
def text(v):
    return "" if v is None else str(v).strip()
 
 
def load_listings(path):
    if not path.exists():
        write_json_template(path)
        print(f"  Created a template at {path}. Add listings to it and run again.")
    try:
        rows = read_rows(path)
    except json.JSONDecodeError as e:
        sys.exit(f"  {path.name} is not valid JSON (line {e.lineno}, column {e.colno}): {e.msg}.\n"
                 "  Check for a missing comma or quote near there.")
    listings, skipped = [], 0
    for n, row in enumerate(rows, 1):
        if row.get("_example") is True:
            continue
        if not any(text(v) for k, v in row.items() if not k.startswith("_")):
            continue  # untouched blank entry
        name, url = text(field(row, "name")), text(field(row, "url"))
        pc = norm_postcode(text(row.get("postcode")))
        price = to_float(field(row, "price"))
        missing = [f for f, v in (("name", name), ("url", url), ("postcode", pc), ("price", price))
                   if not v]
        if missing:
            skipped += 1
            print(f"  Skipped entry {n} ('{name or url or pc or '?'}'): "
                  f"missing required {', '.join(missing)}")
            continue
        listings.append({
            "title": name,
            "url": url,
            "address": text(row.get("address")),
            "postcode": pc,
            "rent_pcm": price,
            "bedrooms": to_int(row.get("bedrooms")),
            "bathrooms": to_int(row.get("bathrooms")),
            "property_type": text(row.get("property_type")),
            "hmo_flag": text(row.get("hmo_licensed")),
            "status": normalise_status(row.get("status")),
            "status_date": text(row.get("status_date")),
            "viewing_date": text(row.get("viewing_date")),
            "agent": text(row.get("agent")),
            "source": text(row.get("source")) or "Your list",
            "available_from": text(row.get("available_from")),
            "notes": text(row.get("notes")),
            "lat": to_float(row.get("lat")),
            "lon": to_float(row.get("lon")),
        })
    print(f"  {len(listings)} listings read from {path.name}"
          + (f", {skipped} skipped for missing required fields" if skipped else ""))
    return listings
 
 
def propertydata(endpoint, **params):
    key = os.environ.get("PROPERTYDATA_API_KEY")
    params["key"] = key
    cache_key = "pd:" + endpoint + ":" + json.dumps({k: v for k, v in params.items()
                                                       if k != "key"}, sort_keys=True)
    data = get_json(f"https://api.propertydata.co.uk/{endpoint}", params=params,
                    cache_key=cache_key)
    if data.get("status") != "success":
        CACHE.pop(cache_key, None)
        raise RuntimeError(data.get("message") or data.get("code") or str(data)[:200])
    return data
 
 
def load_propertydata(min_beds):
    """Asking-rent comparables per area, plus the national HMO licence register."""
    comps, hmos, summaries = [], [], {}
    if not os.environ.get("PROPERTYDATA_API_KEY"):
        print("  PROPERTYDATA_API_KEY not set, skipping PropertyData.")
        return comps, hmos, summaries
 
    for dist_code, (area, lat, lon) in AREAS.items():
        try:
            data = propertydata("rents", postcode=dist_code, bedrooms=min(min_beds, 5))
            long_let = data.get("data", {}).get("long_let", data.get("data", {}))
            avg = long_let.get("average")
            if avg:
                summaries[area] = f"£{avg:,.0f}/week avg asking (PropertyData)" \
                    if isinstance(avg, (int, float)) else str(avg)
            for item in first_list_of_dicts(long_let.get("raw_data", [])):
                la, lo = to_float(pick(item, "lat", "latitude")), to_float(pick(item, "lng", "lon", "longitude"))
                if la is None or lo is None:
                    continue
                comps.append({
                    "area": area, "lat": la, "lon": lo,
                    "rent": pick(item, "price", "rent", "value"),
                    "bedrooms": pick(item, "bedrooms"),
                    "type": pick(item, "type", "property_type"),
                    "url": pick(item, "url", "portal_url", "link") or "",
                })
            print(f"  PropertyData rents {dist_code}: {len(comps)} comparables so far")
        except Exception as e:
            print(f"  PropertyData rents {dist_code} failed: {e}")
 
        try:
            data = propertydata("national-hmo-register", location=f"{lat},{lon}", results=200)
            for item in first_list_of_dicts(data.get("data", data)):
                addr = str(pick(item, "address", "property_address", "full_address") or "")
                pc = norm_postcode(pick(item, "postcode") or find_postcode(addr))
                hmos.append({
                    "address": addr, "postcode": pc,
                    "lat": to_float(pick(item, "lat", "latitude")),
                    "lon": to_float(pick(item, "lng", "lon", "longitude")),
                    "expiry": pick(item, "licence_expiry", "expiry_date", "expiry", "end_date") or "",
                    "max_occupants": pick(item, "max_occupants", "occupants", "max_persons") or "",
                    "council": pick(item, "council", "local_authority") or "",
                })
            print(f"  PropertyData HMO register near {area}: {len(hmos)} licences so far")
        except Exception as e:
            print(f"  PropertyData HMO register near {area} failed: {e}")
 
    # de-duplicate the register (the search circles overlap)
    seen, unique = set(), []
    for h in hmos:
        k = (h["address"].lower(), h["postcode"])
        if k not in seen:
            seen.add(k)
            unique.append(h)
    return comps, unique, summaries
 
 
# ------------------------------------------------------------------ HMO flag --
 
def house_number(address):
    m = re.search(r"\b(\d+[A-Za-z]?)\b", address or "")
    return m.group(1).lower() if m else None
 
 
def flag_hmo(listing, register):
    if listing["hmo_flag"]:
        listing["hmo"] = "Yes (you marked it)" if yes(listing["hmo_flag"]) else "No (you marked it)"
        return
    for h in register:
        if h["postcode"] and h["postcode"] == listing["postcode"]:
            n1, n2 = house_number(listing["address"]), house_number(h["address"])
            if n1 and n1 == n2:
                listing["hmo"] = "Likely, on the HMO licence register"
                return
    text = " ".join([listing["title"], listing["notes"], listing["property_type"]])
    if HMO_KEYWORDS.search(text):
        listing["hmo"] = "Possibly, the ad mentions HMO or sharers"
    else:
        listing["hmo"] = "Unknown, check with the agent"
 
 
# ----------------------------------------------------------------- routing --
 
def resolve_destinations():
    found = geocode_postcodes([d["postcode"] for d in DESTINATIONS.values()])
    for d in DESTINATIONS.values():
        if norm_postcode(d["postcode"]) in found:
            d["lat"], d["lon"] = found[norm_postcode(d["postcode"])]
 
 
def next_weekday():
    d = dt.date.today() + dt.timedelta(days=1)
    while d.weekday() >= 5:
        d += dt.timedelta(days=1)
    return d
 
 
def uk_utc_offset(day):
    """+1h during British Summer Time (last Sunday of March to last Sunday of October)."""
    def last_sunday(month):
        d = dt.date(day.year, month, 31)
        return d - dt.timedelta(days=(d.weekday() + 1) % 7)
    return dt.timedelta(hours=1 if last_sunday(3) <= day < last_sunday(10) else 0)
 
 
def depart_utc(day, hhmm):
    h, m = map(int, hhmm.split(":"))
    local = dt.datetime.combine(day, dt.time(h, m))
    return (local - uk_utc_offset(day)).strftime("%Y-%m-%dT%H:%M:%SZ")
 
 
def shift(hhmm, minutes):
    h, m = map(int, hhmm.split(":"))
    t = dt.datetime(2000, 1, 1, h, m) + dt.timedelta(minutes=minutes)
    return t.strftime("%H:%M")
 
 
def times(typ, lo=None, hi=None, miles=None, route=""):
    lo = typ if lo is None else lo
    hi = typ if hi is None else hi
    return {"typ": typ, "lo": min(lo, typ), "hi": max(hi, typ), "miles": miles, "route": route}
 
 
NO_TIME = {"typ": None, "lo": None, "hi": None, "miles": None, "route": ""}
 
 
# --- Google Maps (Routes API). Needs GOOGLE_MAPS_API_KEY with the Routes API enabled.
 
def google_matrix(points, dest, mode, when_utc, traffic_model=None):
    """Minutes and miles from each point to dest, as Google Maps forecasts them."""
    key = os.environ["GOOGLE_MAPS_API_KEY"]
    results = [None] * len(points)
    for start in range(0, len(points), 25):
        chunk = points[start:start + 25]
        body = {
            "origins": [{"waypoint": {"location": {"latLng": {"latitude": la, "longitude": lo}}}}
                        for la, lo in chunk],
            "destinations": [{"waypoint": {"location": {"latLng": {
                "latitude": dest["lat"], "longitude": dest["lon"]}}}}],
            "travelMode": mode,
            "departureTime": when_utc,
        }
        if mode == "DRIVE":
            body["routingPreference"] = "TRAFFIC_AWARE_OPTIMAL"
            body["trafficModel"] = traffic_model
        ck = "google:" + json.dumps(body, sort_keys=True)
        if ck in CACHE:
            data = CACHE[ck]
        else:
            r = HTTP.post("https://routes.googleapis.com/distanceMatrix/v2:computeRouteMatrix",
                          json=body, timeout=60, headers={
                              "X-Goog-Api-Key": key,
                              "X-Goog-FieldMask": "originIndex,duration,distanceMeters,condition"})
            if r.status_code >= 400:
                raise RuntimeError(f"Google Routes API {r.status_code}: {r.text[:300]}")
            data = CACHE[ck] = r.json()
        for el in data:
            if el.get("condition") == "ROUTE_EXISTS" and "duration" in el:
                mins = round(int(str(el["duration"]).rstrip("s")) / 60)
                results[start + el.get("originIndex", 0)] = (
                    mins, round(el.get("distanceMeters", 0) / 1609.34, 1))
    return results
 
 
# --- Free fallbacks
 
def drive_times_osrm(points, dest):
    """Public OSRM demo server. Free-flow times, no traffic. Keep usage light."""
    results = [None] * len(points)
    for start in range(0, len(points), 80):
        chunk = points[start:start + 80]
        coords = ";".join(f"{lon:.5f},{lat:.5f}" for lat, lon in chunk)
        coords += f";{dest['lon']:.5f},{dest['lat']:.5f}"
        n = len(chunk)
        url = f"https://router.project-osrm.org/table/v1/driving/{coords}"
        params = {"sources": ";".join(map(str, range(n))), "destinations": str(n),
                  "annotations": "duration,distance"}
        data = get_json(url, params=params, cache_key="osrm:" + coords)
        for i in range(n):
            d, m = data["durations"][i][0], data["distances"][i][0]
            if d is not None:
                results[start + i] = (round(d / 60), round(m / 1609.34, 1))
    return results
 
 
def drive_times_ors(points, dest, key):
    """OpenRouteService matrix (free key, 40 requests/min)."""
    results = [None] * len(points)
    for start in range(0, len(points), 50):
        chunk = points[start:start + 50]
        locs = [[lon, lat] for lat, lon in chunk] + [[dest["lon"], dest["lat"]]]
        n = len(chunk)
        ck = "ors:" + json.dumps(locs)
        if ck in CACHE:
            data = CACHE[ck]
        else:
            r = HTTP.post("https://api.openrouteservice.org/v2/matrix/driving-car",
                          json={"locations": locs, "sources": list(range(n)),
                                "destinations": [n], "metrics": ["duration", "distance"],
                                "units": "mi"},
                          headers={"Authorization": key}, timeout=60)
            r.raise_for_status()
            data = CACHE[ck] = r.json()
        for i in range(n):
            d, m = data["durations"][i][0], data["distances"][i][0]
            if d is not None:
                results[start + i] = (round(d / 60), round(m, 1))
    return results
 
 
def drive_times(points, day, depart):
    """Drive to Cody Park leaving at `depart`: best case, typical and worst case."""
    dest = DESTINATIONS["cody"]
    if os.environ.get("GOOGLE_MAPS_API_KEY"):
        try:
            when = depart_utc(day, depart)
            runs = {m: google_matrix(points, dest, "DRIVE", when, m)
                    for m in ("OPTIMISTIC", "BEST_GUESS", "PESSIMISTIC")}
            out = []
            for i in range(len(points)):
                best, typ, worst = (runs[m][i] for m in ("OPTIMISTIC", "BEST_GUESS", "PESSIMISTIC"))
                out.append(times(typ[0], best[0] if best else None, worst[0] if worst else None,
                                 typ[1]) if typ else dict(NO_TIME))
            return out, f"Google Maps traffic forecast, leaving {depart} on {day:%a %d %b}"
        except Exception as e:
            print(f"  Google driving times failed, using the free estimate instead: {e}")
 
    # No Google key: free-flow time scaled by typical morning rush-hour delays
    lo_f, typ_f, hi_f = RUSH_HOUR_FACTORS
    try:
        key = os.environ.get("ORS_API_KEY")
        raw = drive_times_ors(points, dest, key) if key else drive_times_osrm(points, dest)
        engine = "OpenRouteService" if key else "OSRM"
    except Exception as e:
        print(f"  Driving times failed: {e}")
        return [dict(NO_TIME) for _ in points], "unavailable"
    out = [times(round(d * typ_f), round(d * lo_f), round(d * hi_f), miles) if d is not None
           else dict(NO_TIME) for d, miles in (r or (None, None) for r in raw)]
    return out, (f"estimate: {engine} empty-road time x {lo_f}-{hi_f} for {depart} traffic. "
                 "Add GOOGLE_MAPS_API_KEY for real traffic forecasts")
 
 
def tfl_journeys(lat, lon, day, depart):
    """All journey options TfL suggests for leaving at `depart`, fastest first."""
    dest = DESTINATIONS["london"]
    params = {"date": day.strftime("%Y%m%d"), "time": depart.replace(":", ""),
              "timeIs": "Departing", "journeyPreference": "LeastTime"}
    if os.environ.get("TFL_APP_KEY"):
        params["app_key"] = os.environ["TFL_APP_KEY"]
    origin = f"{lat:.5f},{lon:.5f}"
    for to in (f"{dest['lat']},{dest['lon']}", dest["postcode"].replace(" ", "")):
        url = f"https://api.tfl.gov.uk/Journey/JourneyResults/{origin}/to/{to}"
        ck = f"tfl:{origin}:{to}:{params['date']}:{params['time']}"
        try:
            data = get_json(url, params=params, cache_key=ck)
        except Exception:
            continue
        journeys = [j for j in data.get("journeys") or [] if j.get("duration")]
        if not journeys:
            CACHE.pop(ck, None)
            continue
        journeys.sort(key=lambda j: j["duration"])
        modes = []
        for leg in journeys[0].get("legs", []):
            mode = leg.get("mode", {}).get("name", "")
            line = (leg.get("routeOptions") or [{}])[0].get("name", "")
            if mode != "walking":
                modes.append(f"{mode} {line}".strip())
        return [j["duration"] for j in journeys], " > ".join(modes) or "walk"
    return [], ""
 
 
def transit_times(points, day, depart):
    """Public transport to More London leaving around `depart`: fastest, typical, slowest."""
    google = {}
    if os.environ.get("GOOGLE_MAPS_API_KEY"):
        try:
            for offset in TRANSIT_SPREAD_MIN:
                t = shift(depart, offset)
                google[t] = google_matrix(points, DESTINATIONS["london"], "TRANSIT",
                                          depart_utc(day, t))
        except Exception as e:
            print(f"  Google transit times failed, using TfL only: {e}")
            google = {}
 
    out = []
    for i, (lat, lon) in enumerate(points):
        print(f"  TfL journey {i + 1}/{len(points)}", end="\r")
        try:
            tfl, route = tfl_journeys(lat, lon, day, depart)
        except Exception as e:
            print(f"\n  TfL failed for {lat},{lon}: {e}")
            tfl, route = [], ""
        if not os.environ.get("TFL_APP_KEY"):
            time.sleep(0.5)
        g = {t: r[i][0] for t, r in google.items() if r[i]}
        every = tfl + list(g.values())
        if not every:
            out.append(dict(NO_TIME))
            continue
        typ = g.get(depart) or (tfl[0] if tfl else min(every))
        out.append(times(typ, min(every), max(every), route=route))
    print()
    label = f"TfL Journey Planner options leaving {depart}"
    if google:
        label += f", plus Google Maps for departures {', '.join(google)}"
    return out, label + f" on {day:%a %d %b}"
 
 
# ------------------------------------------------------------ commute grid --
 
GRID_FILE = HERE / "commute_grid.json"
 
 
def grid_points(km):
    (south, west), (north, east) = GRID_BOUNDS
    dlat = km / 111.0
    dlon = km / (111.0 * math.cos(math.radians((south + north) / 2)))
    points, lat = [], south + dlat / 2
    while lat < north:
        lon = west + dlon / 2
        while lon < east:
            points.append((round(lat, 5), round(lon, 5)))
            lon += dlon
        lat += dlat
    return points, dlat, dlon
 
 
def build_grid(day, depart, km, rebuild=False):
    """Typical 8am drive time to Cody and transit time to London for every grid square."""
    points, dlat, dlon = grid_points(km)
    use_google = bool(os.environ.get("GOOGLE_MAPS_API_KEY"))
    signature = json.dumps([GRID_BOUNDS, km, depart, use_google, RUSH_HOUR_FACTORS[1],
                            [(d["lat"], d["lon"]) for d in DESTINATIONS.values()]])
    if not rebuild and GRID_FILE.exists():
        try:
            saved = json.loads(GRID_FILE.read_text())
            if saved.get("signature") == signature:
                print(f"  Using the saved commute grid from {saved['made']} "
                      "(add --rebuild-grid to refresh it)")
                return saved
        except Exception:
            pass
 
    print(f"  Working out both commutes for {len(points)} map squares of {km} km")
    cody, office = DESTINATIONS["cody"], DESTINATIONS["london"]
    drive, transit, source = [None] * len(points), [None] * len(points), ""
    if use_google:
        try:
            when = depart_utc(day, depart)
            drive = [r[0] if r else None for r in google_matrix(points, cody, "DRIVE", when, "BEST_GUESS")]
            transit = [r[0] if r else None for r in google_matrix(points, office, "TRANSIT", when)]
            source = "Google Maps typical times"
        except Exception as e:
            print(f"  Google failed for the grid, using the free sources instead: {e}")
            use_google = False
 
    if not use_google:
        try:
            key = os.environ.get("ORS_API_KEY")
            raw = drive_times_ors(points, cody, key) if key else drive_times_osrm(points, cody)
            drive = [round(r[0] * RUSH_HOUR_FACTORS[1]) if r else None for r in raw]
        except Exception as e:
            print(f"  Grid drive times failed: {e}")
        pause = 0.15 if os.environ.get("TFL_APP_KEY") else 1.25
        print(f"  The TfL lookups take about {len(points) * pause / 60 + 1:.0f} minutes the first time. "
              "If you stop it, the next run carries on where it left off.")
        for i, (lat, lon) in enumerate(points):
            print(f"  TfL grid square {i + 1}/{len(points)}", end="\r")
            started = time.monotonic()
            try:
                durations, _ = tfl_journeys(lat, lon, day, depart)
                transit[i] = durations[0] if durations else None
            except Exception:
                pass
            if time.monotonic() - started > 0.05:      # not from the cache, so be polite
                time.sleep(pause)
            if i % 25 == 24:
                save_cache(CACHE)
        print()
        source = "estimated drive (empty roads x rush hour) and TfL journey planner"
 
    grid = {
        "signature": signature,
        "made": f"{dt.date.today():%d %b %Y}",
        "source": source,
        "depart": depart,
        "dlat": dlat, "dlon": dlon,
        "cells": [[la, lo, d, t] for (la, lo), d, t in zip(points, drive, transit)],
    }
    if any(d is not None and t is not None for _, _, d, t in grid["cells"]):
        GRID_FILE.write_text(json.dumps(grid))
    return grid
 
 
def band_colour(minutes):
    for limit, colour, _ in GRID_BANDS:
        if minutes <= limit:
            return colour
    return None
 
 
def place_name(lat, lon):
    """Nearest town or ward name, from postcodes.io reverse lookup."""
    try:
        data = get_json("https://api.postcodes.io/postcodes",
                        params={"lat": lat, "lon": lon, "radius": 2000, "limit": 1},
                        cache_key=f"rev:{lat},{lon}")
        hit = (data.get("result") or [None])[0]
        if hit:
            return f"{hit.get('admin_ward')}, {hit.get('admin_district')} ({hit.get('outcode')})"
    except Exception:
        pass
    return f"{lat:.3f}, {lon:.3f}"
 
 
def best_spots(cells, count=3, min_apart_km=1):
    """Squares where the slower commute is shortest, spread at least min_apart_km apart."""
    ranked = sorted((c for c in cells if c[2] is not None and c[3] is not None),
                    key=lambda c: (max(c[2], c[3]), c[2] + c[3]))
    spots = []
    for c in ranked:
        if all(math.dist((c[0] * 111, c[1] * 69.5), (s[0] * 111, s[1] * 69.5)) >= min_apart_km
               for s in spots):
            spots.append(c)
        if len(spots) == count:
            break
    return spots
 
 
def add_grid_layers(m, grid):
    dlat, dlon, cells = grid["dlat"], grid["dlon"], grid["cells"]
    short = DESTINATIONS["london"]["short"]
    layers = [
        ("Commute hotspots (slower of the two)", lambda d, t: max(d, t) if d is not None and t is not None else None, True),
        ("Drive to Cody only", lambda d, t: d, False),
        (f"Public transport to {short} only", lambda d, t: t, False),
    ]
    for name, value, show in layers:
        group = folium.FeatureGroup(name=name, show=show).add_to(m)
        for lat, lon, d, t in cells:
            v = value(d, t)
            colour = band_colour(v) if v is not None else None
            if not colour:
                continue
            folium.Rectangle(
                bounds=[[lat - dlat / 2, lon - dlon / 2], [lat + dlat / 2, lon + dlon / 2]],
                stroke=False, fill=True, fill_color=colour, fill_opacity=0.45,
                tooltip=f"🚗 Cody {fmt_min(d)} · 🚆 {short} {fmt_min(t)}",
            ).add_to(group)
 
    spots = folium.FeatureGroup(name="Best-balanced spots", show=True).add_to(m)
    for rank, (lat, lon, d, t) in enumerate(best_spots(cells), 1):
        name = place_name(lat, lon)
        folium.Marker(
            [lat, lon],
            tooltip=f"#{rank} best balance: {html.escape(name)}",
            popup=folium.Popup(f"<b>#{rank} best balance</b><br>{html.escape(name)}<br>"
                               f"🚗 Cody: {fmt_min(d)}<br>🚆 {short}: {fmt_min(t)}", max_width=260),
            icon=folium.Icon(color="darkred", icon="star", prefix="fa"),
        ).add_to(spots)
 
 
def grid_legend(grid):
    if not grid:
        return ""
    swatches = " &nbsp;".join(
        f'<span style="white-space:nowrap"><span style="display:inline-block;width:11px;height:11px;'
        f'background:{colour};opacity:.8;vertical-align:-1px"></span> {label}</span>'
        for _, colour, label in GRID_BANDS)
    return (f"<hr style='margin:6px 0'><b>Commute hotspots</b> · slower of the two commutes "
            f"in minutes, leaving {grid['depart']}<br>{swatches}<br>"
            f"<small>★ = best-balanced spots. Squares are "
            f"{f'{GRID_KM * 1000:.0f} m' if GRID_KM < 1 else f'{GRID_KM:g} km'}; "
            f"{html.escape(grid['source'])}, worked out {grid['made']}.</small>")
 
 
# --------------------------------------------------------------------- map --
 
STATUS_STYLE = {label: (pin, hexcol) for label, pin, hexcol, _ in STATUSES}
 
 
def fmt_min(m):
    return f"{m} min" if m is not None else "n/a"
 
 
def fmt_range(l, kind):
    """'62 min (55-80)' from drive_* or transit_* fields."""
    typ, lo, hi = l[f"{kind}_min"], l[f"{kind}_best"], l[f"{kind}_worst"]
    if typ is None:
        return "n/a"
    return f"{typ} min" + (f" ({lo}–{hi})" if lo != hi else "")
 
 
def build_map(listings, comps, hmos, summaries, out_path, drive_label, transit_label, grid=None):
    # OpenStreetMap's own tile servers refuse requests from a local file (no Referer),
    # so the default background is Esri's street map, which works when double-clicked.
    m = folium.Map(location=[51.495, -0.28], zoom_start=13, tiles=None)
    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}",
        attr="Tiles &copy; Esri, HERE, Garmin, &copy; OpenStreetMap contributors",
        name="Street map", control=False,
    ).add_to(m)
    if grid:
        add_grid_layers(m, grid)
 
    # One layer per status, so you can hide e.g. "Not for us" from the layer menu
    groups = {}
    for label, _, hexcol, _ in STATUSES:
        count = sum(1 for l in listings if l["status"] == label)
        if count:
            groups[label] = folium.FeatureGroup(
                name=f'<span style="color:{hexcol}">●</span> {label} ({count})', show=True).add_to(m)
 
    for l in listings:
        e = html.escape
        pin, hexcol = STATUS_STYLE[l["status"]]
        status_line = f"<b style='color:{hexcol}'>{l['status']}</b>"
        if l["status_date"]:
            status_line += f" since {e(l['status_date'])}"
        if l["viewing_date"]:
            status_line += f"<br>Viewing: {e(l['viewing_date'])}"
        extra = ""
        if l["agent"]:
            extra += f"Agent: {e(l['agent'])}<br>"
        if l["available_from"]:
            extra += f"Available: {e(l['available_from'])}<br>"
        if l["notes"]:
            extra += f"<i>{e(l['notes'])}</i><br>"
        link = f'<a href="{e(l["url"])}" target="_blank">Open listing</a>' if l["url"] else ""
        rent = f"£{l['rent_pcm']:,.0f} pcm" if l["rent_pcm"] else "rent n/a"
        pp = f" (£{l['rent_pcm'] / l['bedrooms']:,.0f} per room)" if l["rent_pcm"] and l["bedrooms"] else ""
        miles = f" ({l['drive_miles']} mi)" if l["drive_miles"] else ""
        popup = (
            f"<b>{e(l['title'])}</b><br>{status_line}<br>{e(l['address'])} {e(l['postcode'])}<br>"
            f"{rent}{pp} · {l['bedrooms'] or '?'} bed · {e(l['property_type'])}<br>"
            f"HMO: {e(l['hmo'])}<br>{extra}<hr style='margin:4px 0'>"
            f"<b>Leaving {COMMUTE_DEPART} on a weekday</b> (typical, best–worst)<br>"
            f"🚗 Cody Park: <b>{fmt_range(l, 'drive')}</b>{miles}<br>"
            f"🚆 {DESTINATIONS['london']['short']}: <b>{fmt_range(l, 'transit')}</b><br>"
            f"<small>{e(l['transit_route'])}</small><br>"
            f"<small>Source: {e(l['source'])}</small><br>{link}"
        )
        folium.Marker(
            [l["lat"], l["lon"]],
            popup=folium.Popup(popup, max_width=320),
            tooltip=f"{l['status']} · {rent} · 🚗 {fmt_range(l, 'drive')} · 🚆 {fmt_range(l, 'transit')}",
            icon=folium.Icon(color=pin, icon="home", prefix="fa"),
        ).add_to(groups[l["status"]])
 
    if comps:
        grp = folium.FeatureGroup(name="Asking-rent comparables (PropertyData)", show=False).add_to(m)
        cluster = MarkerCluster().add_to(grp)
        for c in comps:
            txt = f"{c['area']}: {c['bedrooms'] or '?'} bed {c['type'] or ''}, {c['rent'] or ''}"
            if c["url"]:
                txt += f'<br><a href="{html.escape(str(c["url"]))}" target="_blank">link</a>'
            folium.CircleMarker([c["lat"], c["lon"]], radius=5, color="#555", fill=True,
                                popup=txt).add_to(cluster)
 
    hmo_pts = [h for h in hmos if h["lat"] and h["lon"]]
    if hmo_pts:
        grp = folium.FeatureGroup(name="Licensed HMOs (register)", show=False).add_to(m)
        cluster = MarkerCluster().add_to(grp)
        for h in hmo_pts:
            folium.CircleMarker(
                [h["lat"], h["lon"]], radius=5, color="#7b3fe4", fill=True,
                popup=f"{html.escape(h['address'])}<br>Max occupants: {h['max_occupants']}"
                      f"<br>Expires: {h['expiry']}<br>{html.escape(str(h['council']))}",
            ).add_to(cluster)
 
    places = folium.FeatureGroup(name="Work / commute destinations", show=True).add_to(m)
    for d in DESTINATIONS.values():
        folium.Marker([d["lat"], d["lon"]], tooltip=d["name"],
                      icon=folium.Icon(color="cadetblue", icon="briefcase", prefix="fa")).add_to(places)
 
    areas = folium.FeatureGroup(name="Search areas", show=True).add_to(m)
    for code, (name, lat, lon) in AREAS.items():
        folium.Circle([lat, lon], radius=1200, color="#3388ff", weight=1, fill=True,
                      fill_opacity=0.05, tooltip=f"{name} ({code})"
                      + (f": {summaries[name]}" if name in summaries else "")).add_to(areas)
 
    folium.LayerControl(collapsed=False).add_to(m)
    view = [(l["lat"], l["lon"]) for l in listings]
    if grid:
        view += [(c[0], c[1]) for c in grid["cells"]
                 if c[2] is not None and c[3] is not None and max(c[2], c[3]) <= GRID_BANDS[-1][0]]
    if view:
        m.fit_bounds([[min(p[0] for p in view), min(p[1] for p in view)],
                      [max(p[0] for p in view), max(p[1] for p in view)]])
 
    key = " &nbsp;".join(
        f'<span style="white-space:nowrap"><span style="color:{hexcol}">●</span> {label}</span>'
        for label, _, hexcol, _ in STATUSES)
    legend = f"""
    <div style="position:fixed;bottom:18px;left:18px;z-index:9999;background:white;
         padding:10px 12px;border-radius:8px;box-shadow:0 1px 6px rgba(0,0,0,.3);
         font:13px system-ui,sans-serif;max-width:360px">
      <b>{len(listings)} listings</b> · pin colour = status<br>
      {key}<br>
      <small>Times are typical (best–worst) leaving at {COMMUTE_DEPART}.<br>
      Drive: {html.escape(drive_label)}.<br>
      Train: {html.escape(transit_label)}.</small>
      {grid_legend(grid)}
    </div>"""
    m.get_root().html.add_child(folium.Element(legend))
    m.get_root().html.add_child(folium.Element(results_table_html(listings)))
    m.save(str(out_path))
 
 
def results_table_html(listings):
    rows = []
    for l in sorted(listings, key=lambda x: (STATUS_ORDER[x["status"]],
                                             (x["transit_min"] or 999) + (x["drive_min"] or 999))):
        e = html.escape
        hexcol = STATUS_STYLE[l["status"]][1]
        title = f'<a href="{e(l["url"])}" target="_blank">{e(l["title"])}</a>' if l["url"] else e(l["title"])
        rows.append(
            f"<tr><td data-v='{STATUS_ORDER[l['status']]}'><span style='color:{hexcol}'>●</span> "
            f"{l['status']}</td><td>{title}</td><td>{e(l['postcode'])}</td>"
            f"<td data-v='{l['rent_pcm'] or 0}'>{'£{:,.0f}'.format(l['rent_pcm']) if l['rent_pcm'] else ''}</td>"
            f"<td data-v='{l['bedrooms'] or 0}'>{l['bedrooms'] or ''}</td><td>{e(l['hmo'])}</td>"
            f"<td data-v='{l['drive_min'] or 999}'>{fmt_range(l, 'drive')}</td>"
            f"<td data-v='{l['transit_min'] or 999}'>{fmt_range(l, 'transit')}</td>"
            f"<td>{e(l['source'])}</td></tr>")
    return f"""
    <details id="tbl" style="position:fixed;top:12px;left:56px;z-index:9999;background:white;
       border-radius:8px;box-shadow:0 1px 6px rgba(0,0,0,.3);font:13px system-ui,sans-serif;
       max-width:calc(100vw - 280px);max-height:70vh;overflow:auto;padding:6px 10px">
      <summary style="cursor:pointer;font-weight:600">Table view (click a heading to sort)</summary>
      <table style="border-collapse:collapse;margin-top:6px">
        <thead><tr style="text-align:left">
          <th>Status</th><th>Listing</th><th>Postcode</th><th>Rent</th><th>Beds</th><th>HMO</th>
          <th>🚗 Cody at {COMMUTE_DEPART}</th><th>🚆 {DESTINATIONS['london']['short']} at {COMMUTE_DEPART}</th><th>Source</th></tr></thead>
        <tbody>{''.join(rows)}</tbody>
      </table>
    </details>
    <style>#tbl th,#tbl td{{padding:3px 8px;border-bottom:1px solid #eee;white-space:nowrap}}
           #tbl th{{cursor:pointer;position:sticky;top:0;background:#fff}}</style>
    <script>
      document.querySelectorAll('#tbl th').forEach((th, i) => th.onclick = () => {{
        const tb = th.closest('table').tBodies[0], rows = [...tb.rows];
        const asc = th.dataset.asc = th.dataset.asc === '1' ? '0' : '1';
        const val = r => r.cells[i].dataset.v ?? r.cells[i].innerText.toLowerCase();
        rows.sort((a, b) => {{ const x = val(a), y = val(b);
          const c = isNaN(x) || isNaN(y) ? String(x).localeCompare(y) : x - y;
          return asc === '1' ? c : -c; }});
        rows.forEach(r => tb.appendChild(r));
      }});
    </script>"""
 
 
def write_results_csv(listings, path):
    cols = ["status", "status_date", "viewing_date", "title", "url", "address", "postcode", "area", "rent_pcm", "bedrooms", "bathrooms",
            "property_type", "hmo", "drive_min", "drive_best", "drive_worst", "drive_miles",
            "transit_min", "transit_best", "transit_worst", "transit_route",
            "agent", "source", "available_from", "notes", "lat", "lon"]
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
        w.writeheader()
        for l in listings:
            w.writerow(l)
 
 
# -------------------------------------------------------------------- main --
 
def main():
    global COMMUTE_DEPART, GRID_KM
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("--listings", "--csv", default=str(HERE / "listings.json"),
                    help="your listings file (listings.json, or a .csv with the same fields)")
    ap.add_argument("--min-beds", type=int, default=MIN_BEDS)
    ap.add_argument("--any-area", action="store_true",
                    help="keep listings outside W3/W4/TW8 instead of dropping them")
    ap.add_argument("--hmo-only", action="store_true",
                    help="drop listings with no sign of an HMO licence")
    ap.add_argument("--out", default=str(HERE / "house_map.html"))
    ap.add_argument("--open", action="store_true", help="open the map in your browser")
    ap.add_argument("--no-grid", action="store_true",
                    help="skip the commute hotspot layer")
    ap.add_argument("--rebuild-grid", action="store_true",
                    help="recalculate the commute hotspot layer instead of reusing commute_grid.json")
    ap.add_argument("--grid-km", type=float, default=GRID_KM,
                    help=f"size of each hotspot square in km (default {GRID_KM}; smaller = slower)")
    ap.add_argument("--depart", default=COMMUTE_DEPART, metavar="HH:MM",
                    help=f"time you leave home on a weekday (default {COMMUTE_DEPART})")
    args = ap.parse_args()
 
    print("1/5 Loading listings")
    listings = load_listings(Path(args.listings))
    comps, hmos, summaries = load_propertydata(args.min_beds)
 
    print("2/5 Locating listings")
    resolve_destinations()
    coords = geocode_postcodes([l["postcode"] for l in listings])
    coords.update(geocode_postcodes([h["postcode"] for h in hmos if h["postcode"] and not h["lat"]]))
    for h in hmos:
        if not h["lat"] and h["postcode"] in coords:
            h["lat"], h["lon"] = coords[h["postcode"]]
    for l in listings:
        if l["lat"] is None and l["postcode"] in coords:
            l["lat"], l["lon"] = coords[l["postcode"]]
        if l["lat"] is None and l["address"]:
            hit = geocode_address(l["address"] + ", London")
            if hit:
                l["lat"], l["lon"] = hit
    missing = [l["title"] for l in listings if l["lat"] is None]
    if missing:
        print(f"  Could not place {len(missing)} listing(s), add a postcode or lat/lon: {missing}")
    listings = [l for l in listings if l["lat"] is not None]
 
    print("3/5 Filtering")
    kept = []
    for l in listings:
        l["area"] = AREAS.get(district(l["postcode"]), ("Outside target areas",))[0]
        if l["bedrooms"] is not None and l["bedrooms"] < args.min_beds:
            continue
        if not args.any_area and l["area"] == "Outside target areas":
            continue
        flag_hmo(l, hmos)
        if args.hmo_only and not (l["hmo"].startswith(("Yes", "Likely", "Possibly"))):
            continue
        kept.append(l)
    print(f"  {len(kept)} of {len(listings)} listings match "
          f"({args.min_beds}+ bed{'' if args.any_area else ', W3/W4/TW8'}"
          f"{', HMO only' if args.hmo_only else ''})")
    listings = kept
 
    print("4/5 Commute times")
    points = [(l["lat"], l["lon"]) for l in listings]
    COMMUTE_DEPART = args.depart
    day = next_weekday()
    print(f"  Leaving at {args.depart} on {day:%A %d %B}")
    drives, drive_label = drive_times(points, day, args.depart) if points else ([], "n/a")
    transits, transit_label = transit_times(points, day, args.depart) if points else ([], "n/a")
    for l, d, t in zip(listings, drives, transits):
        l["drive_min"], l["drive_best"], l["drive_worst"], l["drive_miles"] = \
            d["typ"], d["lo"], d["hi"], d["miles"]
        l["transit_min"], l["transit_best"], l["transit_worst"], l["transit_route"] = \
            t["typ"], t["lo"], t["hi"], t["route"]
    save_cache(CACHE)
 
    grid = None
    if not args.no_grid:
        GRID_KM = args.grid_km
        grid = build_grid(day, args.depart, args.grid_km, args.rebuild_grid)
        save_cache(CACHE)
 
    print("5/5 Writing outputs")
    out = Path(args.out)
    build_map(listings, comps, hmos, summaries, out, drive_label, transit_label, grid)
    write_results_csv(listings, out.with_name("results.csv"))
    print(f"  Map:   {out}\n  Table: {out.with_name('results.csv')}")
    if args.open:
        webbrowser.open(out.resolve().as_uri())
 
 
if __name__ == "__main__":
    main()
 
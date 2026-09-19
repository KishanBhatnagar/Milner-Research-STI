"""
nsfg_active.py -- % sexually active in the past 12 months by sex and age, for every
NSFG public-use release from 2000 to 2023:

    2002, 2006_2010, 2011_2013, 2013_2015, 2015_2017, 2017_2019, 2022_2023

(No NSFG data were collected between 2019 and 2022.)

Same method as the nsfg-raw-data-to-sexually-active-percentage skill, applied identically
to every cycle. "Sexually active" = ANY sex (vaginal, oral or anal; opposite- or same-sex
partner) in the 12 months before the interview.

DEFINITIONS
  SEX     which respondent file the row came from (female vs male file)
  AGER    age at interview
  ACTIVE  (main result, "any sex") -- the UNION of three reports:
            PARTS1YR   > 0   opposite-sex partners, vaginal intercourse (interviewer section)
            OPPYEARNUM > 0   opposite-sex sexual partners (private ACASI section)
            SAMYEARNUM > 0   same-sex sexual partners (private ACASI section)
          1 if ANY of them reports >= 1 partner, including "don't know how many"
            (OPPYEARNUM/SAMYEARNUM = DK code) -- one report of sex anywhere is enough.
          0 if every usable answer says zero. HADSEX == 2 (never had vaginal intercourse)
            only zeroes the vaginal part; it cannot rule out oral/anal/same-sex contact.
          missing if no part gives a usable answer -> dropped and reported by age.
          If a file lacks OPPYEARNUM and/or SAMYEARNUM, the definition falls back to what
          is available and the cycle/sex is FLAGGED as narrower in the output and log.
  ACTIVE_VAG  (comparison column pct_active_vaginal) -- the earlier definition:
          PARTS1YR > 0; 0 if PARTS1YR == 0 or HADSEX == 2.
  WEIGHT  the cycle's final respondent weight (each person stands in for that many people)
  pct     sum(ACTIVE * WEIGHT) / sum(WEIGHT) within each cell; 5-year bands pool everyone
          in the band (NOT a mean of single-year %s) and are verified against a rebuild.

USAGE
  Put the raw files in one folder (default ./nsfg_data; subfolders are searched too):
    2002-2019:  <cycle> female + male .dat files and their Stata .dct (or SAS .sas) setups
    2022-2023:  the female + male public-use .sas7bdat or .csv files

  python nsfg_active.py --list                       # what each cycle needs
  python nsfg_active.py --download 2017_2019         # optional: try fetching from the CDC FTP
  python nsfg_active.py --cycles 2015_2017 2017_2019
  python nsfg_active.py --cycles all --max-age 44    # common 15-44 range for comparisons

  In a notebook:
    import nsfg_active as na
    res = na.run_cycle("2017_2019", data_dir="nsfg_data")
    res["by_band"]
    combined = na.run_all(["2015_2017", "2017_2019"], data_dir="nsfg_data")

OUTPUT (in --out, default ./nsfg_results)
  <cycle>/by_age.csv, by_band.csv, counts_by_age.csv, counts_by_band.csv, dropped_by_age.csv
  all_cycles_by_age.csv, all_cycles_by_band.csv
  run_log.json   python/pandas versions, SHA-256 of every input file, settings used

Requires: pandas (>=1.5). Reading .sas7bdat uses pandas.read_sas (no extra package).
"""
from __future__ import annotations

import argparse
import datetime as dt
import glob
import hashlib
import json
import os
import platform
import re
import sys
import urllib.request

import pandas as pd

# =============================================================================
# Cycle configuration -- the ONLY place cycles differ
# =============================================================================
FTP_OLD = "https://ftp.cdc.gov/pub/Health_Statistics/NCHS/Datasets/NSFG/"
FTP_NEW = "https://ftp.cdc.gov/pub/Health_Statistics/NCHS/NSFG/"


def _fwf(cycle, fem, male, weight, ages, cluster=("SECU", "SECU_R"), stratum=("SEST",)):
    """Config for a fixed-width (.dat + .dct) release."""
    return dict(kind="fwf", fem=fem, male=male, weight=weight, ages=ages,
                cluster=cluster, stratum=stratum,
                # setup-file name candidates for --download (stata/ subfolder)
                fem_setup=[f"{cycle}_FemRespSetup.dct", f"{cycle}FemRespSetup.dct",
                           f"{cycle}FemResp.dct", f"{cycle}_FemResp.dct"],
                male_setup=[f"{cycle}_MaleSetup.dct", f"{cycle}MaleSetup.dct",
                            f"{cycle}Male.dct", f"{cycle}_Male.dct"])


CYCLES = {
    "2002":      _fwf("2002", "2002FemResp.dat", "2002Male.dat", "FINALWGT", (15, 44),
                      cluster=("SECU_R", "SECU")),
    "2006_2010": _fwf("2006_2010", "2006_2010_FemResp.dat", "2006_2010_Male.dat",
                      "WGTQ1Q16", (15, 44)),
    "2011_2013": _fwf("2011_2013", "2011_2013_FemRespData.dat", "2011_2013_MaleData.dat",
                      "WGT2011_2013", (15, 44)),
    "2013_2015": _fwf("2013_2015", "2013_2015_FemRespData.dat", "2013_2015_MaleData.dat",
                      "WGT2013_2015", (15, 44)),
    "2015_2017": _fwf("2015_2017", "2015_2017_FemRespData.dat", "2015_2017_MaleData.dat",
                      "WGT2015_2017", (15, 49)),
    "2017_2019": _fwf("2017_2019", "2017_2019_FemRespData.dat", "2017_2019_MaleData.dat",
                      "WGT2017_2019", (15, 49)),
    "2022_2023": dict(kind="puf", weight="WGT2022_2023", ages=(15, 49),
                      cluster=("VECL",), stratum=("VEST",),
                      # filename patterns searched in data_dir (.sas7bdat preferred, else .csv)
                      fem_glob="*2022*2023*Fem*Resp*", male_glob="*2022*2023*Male*",
                      fem_urls=[FTP_NEW + "NSFG-2022-2023-FemRespPUFData.sas7bdat"],
                      male_urls=[FTP_NEW + "NSFG-2022-2023-MaleRespPUFData.sas7bdat",
                                 FTP_NEW + "NSFG-2022-2023-MalePUFData.sas7bdat"]),
}

MISSING_MIN = 97      # PARTS1YR >= this = not ascertained / refused / don't know
THIN_CELL = 100       # flag single-year cells with fewer respondents than this
BAND_WIDTH = 5
# OPPYEARNUM / SAMYEARNUM coding (confirm in each cycle's codebook; printed in step [1]):
PRIVATE_MAX_COUNT = 995       # 0..995 are partner counts (995 = top-code)
PRIVATE_DK_CODES = {998}      # "don't know how many" -> had >= 1 partner -> active
                              # any other value > 995 (e.g. 997, 999 refused) = unusable
PRIVATE_VARS = ["OPPYEARNUM", "SAMYEARNUM"]
NEEDED = ["CASEID", "AGER", "HADSEX", "PARTS1YR", "PARTS1YR_I"] + PRIVATE_VARS


def normalize_cycle(text: str) -> str:
    t = str(text).strip().replace("-", "_")
    if t in CYCLES:
        return t
    years = [int(y) + (2000 if len(y) == 2 else 0) for y in re.findall(r"\d{2,4}", t)]
    if len(years) == 2 and f"{years[0]}_{years[1]}" in CYCLES:
        return f"{years[0]}_{years[1]}"
    if len(years) == 1:
        y = years[0]
        hits = [k for k in CYCLES if k == str(y) or
                ("_" in k and int(k[:4]) <= y <= int(k[5:]))]
        if len(hits) == 1:
            return hits[0]
        if len(hits) > 1:
            raise ValueError(f"{y} is in more than one cycle ({', '.join(hits)}); name the cycle.")
    raise ValueError(f"Unknown NSFG cycle '{text}'. Options: {', '.join(CYCLES)}")


# =============================================================================
# Reading
# =============================================================================
def parse_setup(path: str) -> dict:
    """{VARNAME: (start0, end0)} from a Stata .dct or a SAS column-input setup file."""
    text = open(path, errors="ignore").read()
    specs = {}
    if path.lower().endswith(".dct"):
        for m in re.finditer(r"_column\((\d+)\)\s+\S+\s+(\w+)\s+%(\d+)", text):
            start, name, width = int(m[1]) - 1, m[2].upper(), int(m[3])
            specs[name] = (start, start + width)
    else:
        block = re.search(r"\bINPUT\b(.*?);", text, re.S | re.I)
        body = block.group(1) if block else text
        for m in re.finditer(r"\b([A-Za-z_]\w*)\s+(?:\$\s*)?(\d+)(?:\s*-\s*(\d+))?", body):
            specs[m[1].upper()] = (int(m[2]) - 1, int(m[3] or m[2]))
    if not specs:
        raise ValueError(f"No column positions could be parsed from {path}")
    return specs


def _find(data_dir: str, patterns: list[str]) -> list[str]:
    hits = set()
    for p in patterns:
        hits.update(glob.glob(os.path.join(data_dir, "**", p), recursive=True))
    return sorted(hits, key=lambda h: (len(h), h))


def _find_setup(data_dir, cycle, words):
    cands = _find(data_dir, [f"*{cycle}*{w}*{ext}" for w in words for ext in (".dct", ".sas")])
    cands = [c for c in cands if not c.lower().endswith(".sas7bdat")
             and not re.search(r"preg|wgt|hhvar|curr_ins", os.path.basename(c), re.I)]
    # prefer .dct, then names containing the first (most specific) word, e.g. "FemResp"
    cands.sort(key=lambda h: (not h.lower().endswith(".dct"),
                              words[0].lower() not in os.path.basename(h).lower(), len(h)))
    if not cands:
        raise FileNotFoundError(f"No .dct/.sas setup file for {cycle} ({'/'.join(words)}) "
                                f"under {data_dir}. Get it from {FTP_OLD}stata/")
    return cands[0]


def _pick(names, candidates):
    return next((c for c in candidates if c in names), None)


def _choose_weight(names, expected):
    if expected in names:
        return expected
    alt = sorted(n for n in names if n.startswith("WGT") or n == "FINALWGT")
    return alt[0] if alt else None


def _standardize(df, cfg, sex, cycle, source):
    names = set(df.columns)
    weight = _choose_weight(names, cfg["weight"])
    cluster, stratum = _pick(names, cfg["cluster"]), _pick(names, cfg["stratum"])
    missing = [v for v in ("CASEID", "AGER", "PARTS1YR") if v not in names] + \
              ([] if weight else ["<weight>"])
    if missing:
        raise KeyError(f"{cycle} {sex}: required variable(s) not found in {source}: {missing}")
    keep = {c: c for c in NEEDED if c in names}
    keep.update({weight: "WEIGHT"})
    if cluster:
        keep[cluster] = "CLUSTER"
    if stratum:
        keep[stratum] = "STRATUM"
    out = df[list(keep)].rename(columns=keep).copy()
    for v in PRIVATE_VARS + ["HADSEX"]:
        if v not in out:
            out[v] = pd.NA
    out["SEX"], out["CYCLE"] = sex, cycle
    absent = [v for v in PRIVATE_VARS if v not in names]
    definition = ("any sex (full)" if not absent else
                  "vaginal only (FALLBACK: no " + ", ".join(absent) + ")"
                  if len(absent) == len(PRIVATE_VARS) else
                  "partial (NARROWER: no " + ", ".join(absent) + ")")
    meta = dict(file=os.path.basename(source), rows=len(out), weight=weight,
                cluster=cluster, stratum=stratum, has_hadsex="HADSEX" in names,
                has_imputation_flag="PARTS1YR_I" in names,
                private_vars_missing=absent, definition=definition)
    return out, meta


def _read_fwf_file(data_dir, cycle, cfg, sex):
    dat_name = cfg["fem"] if sex == "F" else cfg["male"]
    dat = _find(data_dir, [dat_name])
    if not dat:
        raise FileNotFoundError(f"{dat_name} not found under {data_dir}. Get it from {FTP_OLD}")
    setup = _find_setup(data_dir, cycle, ["FemResp", "Fem"] if sex == "F" else ["Male"])
    specs = parse_setup(setup)
    weight = _choose_weight(specs, cfg["weight"])
    cols = [c for c in NEEDED + [weight, *cfg["cluster"], *cfg["stratum"]]
            if c and c in specs]
    cols = list(dict.fromkeys(cols))
    df = pd.read_fwf(dat[0], colspecs=[specs[c] for c in cols], names=cols,
                     header=None, dtype={"CASEID": str})
    out, meta = _standardize(df, cfg, sex, cycle, dat[0])
    meta["setup"] = os.path.basename(setup)
    return out, meta, [dat[0], setup]


def _read_puf_file(data_dir, cycle, cfg, sex):
    pat = cfg["fem_glob"] if sex == "F" else cfg["male_glob"]
    files = _find(data_dir, [pat + ".sas7bdat", pat + ".csv"])
    if sex == "M":
        files = [f for f in files if "fem" not in os.path.basename(f).lower()]
    files = [f for f in files if "preg" not in os.path.basename(f).lower()]
    if not files:
        raise FileNotFoundError(f"No {cycle} {'female' if sex == 'F' else 'male'} "
                                f".sas7bdat/.csv under {data_dir}. Get it from {FTP_NEW}")
    files.sort(key=lambda f: not f.lower().endswith(".sas7bdat"))
    path = files[0]
    df = (pd.read_sas(path, format="sas7bdat", encoding="latin-1")
          if path.lower().endswith(".sas7bdat") else pd.read_csv(path, low_memory=False))
    df.columns = [c.upper() for c in df.columns]
    df["CASEID"] = df["CASEID"].astype(str)
    out, meta = _standardize(df, cfg, sex, cycle, path)
    return out, meta, [path]


def load_cycle(cycle: str, data_dir: str = "nsfg_data"):
    """Return (stacked respondent-level DataFrame, metadata, list of input files)."""
    cycle = normalize_cycle(cycle)
    cfg = CYCLES[cycle]
    reader = _read_fwf_file if cfg["kind"] == "fwf" else _read_puf_file
    parts, metas, files = [], {}, []
    for sex in ("F", "M"):
        df, meta, used = reader(data_dir, cycle, cfg, sex)
        parts.append(df)
        metas[sex] = meta
        files += used
    return pd.concat(parts, ignore_index=True), metas, files


# =============================================================================
# Estimation
# =============================================================================
def band_edges(age_min, age_max, width=BAND_WIDTH):
    edges = [age_min - 1] + list(range(age_min - 1 + width, age_max + 1, width))
    if edges[-1] != age_max:
        edges.append(age_max)
    labels = [f"{a + 1}-{b}" for a, b in zip(edges[:-1], edges[1:])]
    return edges, labels


def derive_active(df: pd.DataFrame):
    """Add ACTIVE (any sex, union), ACTIVE_VAG (old definition) and SOURCE.
    Return (rows with usable ACTIVE, rows dropped as unusable)."""
    num = lambda c: pd.to_numeric(df[c], errors="coerce")
    never_vag = num("HADSEX") == 2

    # vaginal / interviewer-section part
    v = num("PARTS1YR")
    v = v.where(v < MISSING_MIN)
    vag_pos = v > 0
    vag_usable = v.notna() | never_vag
    active_vag = (v > 0).astype("float").where(v.notna()).mask(never_vag, 0.0)

    # private-section parts
    priv_pos = pd.Series(False, index=df.index)
    priv_usable = pd.Series(False, index=df.index)
    same_pos = pd.Series(False, index=df.index)
    for var in PRIVATE_VARS:
        x = num(var)
        count_ok = x.between(0, PRIVATE_MAX_COUNT)
        pos = (count_ok & (x > 0)) | x.isin(PRIVATE_DK_CODES)
        priv_pos |= pos
        priv_usable |= count_ok | x.isin(PRIVATE_DK_CODES)
        if var == "SAMYEARNUM":
            same_pos = pos

    any_pos = vag_pos | priv_pos
    usable = vag_usable | priv_usable
    active = pd.Series(float("nan"), index=df.index)
    active[usable] = 0.0
    active[any_pos] = 1.0

    source = pd.Series("not active", index=df.index)
    source[vag_pos & priv_pos] = "both"
    source[~vag_pos & priv_pos] = "private only"
    source[vag_pos & ~priv_pos] = "vaginal only"
    source[active.isna()] = "unusable"

    df = df.assign(PARTS1YR_CLEAN=v, ACTIVE=active, ACTIVE_VAG=active_vag,
                   SAME_SEX_ACTIVE=same_pos.astype(int), SOURCE=source)
    return df[df["ACTIVE"].notna()].copy(), df[df["ACTIVE"].isna()].copy()


def weighted_pct(df, keys, col="ACTIVE", name="pct_active"):
    d = df[df[col].notna()]
    d = d.assign(_AW=d[col] * d["WEIGHT"])
    g = d.groupby(keys, observed=True).agg(n_unweighted=(col, "size"),
                                           weighted_pop=("WEIGHT", "sum"),
                                           _aw=("_AW", "sum"))
    g[name] = 100 * g["_aw"] / g["weighted_pop"]
    return g.drop(columns="_aw").reset_index()


def _with_vaginal(df, keys, main):
    old = weighted_pct(df, keys, "ACTIVE_VAG", "pct_active_vaginal")[keys + ["pct_active_vaginal"]]
    out = main.merge(old, on=keys, how="left")
    out["pct_difference"] = out["pct_active"] - out["pct_active_vaginal"]
    return out


def estimate(df, age_min, age_max):
    edges, labels = band_edges(age_min, age_max)
    df = df[(df["AGER"] >= age_min) & (df["AGER"] <= age_max)].copy()
    df["AGEGRP"] = pd.cut(df["AGER"], edges, labels=labels)      # right-inclusive
    by_age = _with_vaginal(df, ["CYCLE", "SEX", "AGER"], weighted_pct(df, ["CYCLE", "SEX", "AGER"]))
    by_band = _with_vaginal(df, ["CYCLE", "SEX", "AGEGRP"],
                            weighted_pct(df, ["CYCLE", "SEX", "AGEGRP"]))
    by_band["AGEGRP"] = by_band["AGEGRP"].astype(str)
    source = pd.crosstab([df["SEX"], df["AGEGRP"]], df["SOURCE"])

    # band check: pooled band % must equal population-weighted mean of single-year %s
    a = by_age.copy()
    a["AGEGRP"] = pd.cut(a["AGER"], edges, labels=labels).astype(str)
    a["_pw"] = a["pct_active"] * a["weighted_pop"]
    grp = a.groupby(["CYCLE", "SEX", "AGEGRP"])
    check = pd.DataFrame({"pct_rebuilt": grp["_pw"].sum() / grp["weighted_pop"].sum(),
                          "pct_simple_mean": grp["pct_active"].mean()})
    check = by_band.set_index(["CYCLE", "SEX", "AGEGRP"])[["pct_active"]].join(check)
    worst = (check["pct_active"] - check["pct_rebuilt"]).abs().max()
    assert worst < 1e-9, f"band pooling check failed (max diff {worst})"

    counts_age = pd.crosstab(df["AGER"], df["SEX"], margins=True, margins_name="Total")
    counts_band = pd.crosstab(df["AGEGRP"], df["SEX"], margins=True, margins_name="Total")
    cells = counts_age.drop(index="Total").drop(columns="Total").stack()
    thin = cells[cells < THIN_CELL].rename("n").reset_index()
    return dict(data=df, by_age=by_age, by_band=by_band, band_check=check.reset_index(),
                source_by_band=source,
                counts_by_age=counts_age, counts_by_band=counts_band, thin_cells=thin)


# =============================================================================
# Running, reporting, saving
# =============================================================================
def _sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run_cycle(cycle, data_dir="nsfg_data", out_dir=None, max_age=None, verbose=True):
    cycle = normalize_cycle(cycle)
    age_min, age_max = CYCLES[cycle]["ages"]
    if max_age:
        age_max = min(age_max, max_age)
    raw, meta, files = load_cycle(cycle, data_dir)
    kept, dropped = derive_active(raw)
    res = estimate(kept, age_min, age_max)
    res.update(meta=meta, files=files, raw=raw, dropped=dropped,
               ages=(age_min, age_max))
    defs = {sex: m["definition"] for sex, m in meta.items()}
    for key in ("by_age", "by_band"):
        res[key]["definition"] = res[key]["SEX"].map(defs)
    res["dropped_by_age"] = pd.crosstab(dropped["AGER"], dropped["SEX"]) if len(dropped) \
        else pd.DataFrame()
    if "HADSEX" in raw:
        blank = pd.to_numeric(raw["PARTS1YR"], errors="coerce").isna()
        res["blank_parts_vs_hadsex"] = pd.crosstab([raw["SEX"], blank.rename("PARTS1YR_blank")],
                                                   raw["HADSEX"].fillna("absent"))
    if verbose:
        _report(cycle, res)
    if out_dir:
        d = os.path.join(out_dir, cycle)
        os.makedirs(d, exist_ok=True)
        res["by_age"].to_csv(os.path.join(d, "by_age.csv"), index=False)
        res["by_band"].to_csv(os.path.join(d, "by_band.csv"), index=False)
        res["band_check"].to_csv(os.path.join(d, "band_check.csv"), index=False)
        res["counts_by_age"].to_csv(os.path.join(d, "counts_by_age.csv"))
        res["counts_by_band"].to_csv(os.path.join(d, "counts_by_band.csv"))
        res["dropped_by_age"].to_csv(os.path.join(d, "dropped_by_age.csv"))
        res["source_by_band"].to_csv(os.path.join(d, "source_by_band.csv"))
    return res


def _report(cycle, r):
    pd.set_option("display.width", 160)
    pd.set_option("display.max_columns", None)
    line = "=" * 78
    print(f"\n{line}\nNSFG {cycle}  (ages {r['ages'][0]}-{r['ages'][1]})\n{line}")
    for sex, m in r["meta"].items():
        print(f"{sex}: {m['file']}{' + ' + m['setup'] if 'setup' in m else ''} -> {m['rows']:,} rows; "
              f"weight={m['weight']} cluster={m['cluster']} stratum={m['stratum']} "
              f"HADSEX={'yes' if m['has_hadsex'] else 'NO'}")
        flag = "" if m["definition"] == "any sex (full)" else "   <-- NARROWER THAN 'ANY SEX'"
        print(f"   definition used: {m['definition']}{flag}")
    raw = r["raw"]
    print("\n[1] Sanity checks")
    print(raw.groupby("SEX")["AGER"].agg(["count", "min", "max"]))
    print("Weighted population by sex:",
          {k: f"{v:,.0f}" for k, v in raw.groupby("SEX")["WEIGHT"].sum().items()})
    print("PARTS1YR values (confirm codes against the codebook):")
    print(raw["PARTS1YR"].value_counts(dropna=False).sort_index().to_string())
    for var in PRIVATE_VARS:
        x = pd.to_numeric(raw[var], errors="coerce")
        if x.notna().any():
            codes = x[x > PRIVATE_MAX_COUNT].value_counts().sort_index()
            print(f"{var}: {int((x == 0).sum())} zero, "
                  f"{int(x.between(1, PRIVATE_MAX_COUNT).sum())} with >=1 partner, "
                  f"{int(x.isna().sum())} blank; special codes { {int(k): int(v) for k, v in codes.items()} } "
                  f"(DK={sorted(PRIVATE_DK_CODES)} counted active; confirm in codebook)")
    if "blank_parts_vs_hadsex" in r:
        print("\nBlank PARTS1YR vs HADSEX (1=yes, 2=never). HADSEX=2 zeroes only the vaginal "
              "part; the private-section answers can still make someone active:")
        print(r["blank_parts_vs_hadsex"])
    print(f"\n[2] Dropped (no usable answer): {len(r['dropped'])} rows")
    if len(r["dropped"]):
        print(r["dropped_by_age"])
    if "PARTS1YR_I" in r["data"]:
        print("PARTS1YR imputation flag counts by sex:")
        print(pd.crosstab(r["data"]["SEX"], r["data"]["PARTS1YR_I"]))
    print("\nWhere each 'yes' came from: both = vaginal (PARTS1YR) and private section agree; "
          "private only = oral/anal/same-sex reported privately only; vaginal only = PARTS1YR>0 but "
          "private section said 0 or blank:")
    print(r["source_by_band"])
    print("\n[3] % sexually active (any sex), 5-year bands; pct_active_vaginal = old "
          "PARTS1YR-only definition for comparison")
    print(r["by_band"].drop(columns=["CYCLE", "definition"])
          .round({"pct_active": 1, "pct_active_vaginal": 1, "pct_difference": 1,
                  "weighted_pop": 0}).to_string(index=False))
    print("\n% sexually active (any sex), single year of age")
    print(r["by_age"].pivot(index="AGER", columns="SEX", values="pct_active").round(1))
    print("\n[4] Respondents per cell")
    print(r["counts_by_band"])
    print(f"Single-year cells with n < {THIN_CELL}: "
          + (", ".join(f"{a}{s}={n}" for a, s, n in r["thin_cells"].itertuples(index=False))
             or "none"))
    print("\n[5] Band check (pct_rebuilt == pct_active; simple mean for contrast)")
    print(r["band_check"].drop(columns="CYCLE").round(2).to_string(index=False))


def run_all(cycles, data_dir="nsfg_data", out_dir="nsfg_results", max_age=None, verbose=True):
    cycles = list(CYCLES) if cycles in ("all", ["all"]) else [normalize_cycle(c) for c in cycles]
    results, log = {}, dict(
        run_at=dt.datetime.now().isoformat(timespec="seconds"),
        python=sys.version.split()[0], pandas=pd.__version__, platform=platform.platform(),
        settings=dict(definition="any sex = PARTS1YR>0 | OPPYEARNUM>0 | SAMYEARNUM>0 (DK=active)",
                      private_max_count=PRIVATE_MAX_COUNT, private_dk_codes=sorted(PRIVATE_DK_CODES),
                      missing_min=MISSING_MIN, thin_cell=THIN_CELL, band_width=BAND_WIDTH,
                      max_age=max_age, data_dir=os.path.abspath(data_dir)),
        cycles={})
    for c in cycles:
        try:
            r = run_cycle(c, data_dir, out_dir, max_age, verbose)
        except (FileNotFoundError, KeyError, ValueError) as e:
            print(f"\n!! Skipping {c}: {e}")
            log["cycles"][c] = dict(status="skipped", reason=str(e))
            continue
        results[c] = r
        log["cycles"][c] = dict(status="ok", ages=r["ages"], meta=r["meta"],
                                definition={s_: m["definition"] for s_, m in r["meta"].items()},
                                dropped_rows=len(r["dropped"]),
                                inputs={os.path.basename(f): _sha256(f) for f in r["files"]})
    if results and out_dir:
        os.makedirs(out_dir, exist_ok=True)
        pd.concat([r["by_age"] for r in results.values()]).to_csv(
            os.path.join(out_dir, "all_cycles_by_age.csv"), index=False)
        pd.concat([r["by_band"] for r in results.values()]).to_csv(
            os.path.join(out_dir, "all_cycles_by_band.csv"), index=False)
        with open(os.path.join(out_dir, "run_log.json"), "w") as f:
            json.dump(log, f, indent=2, default=str)
        if verbose:
            wide = pd.concat([r["by_band"] for r in results.values()]).pivot_table(
                index="AGEGRP", columns=["SEX", "CYCLE"], values="pct_active").round(1)
            print(f"\n{'=' * 78}\nAll cycles: % sexually active (any sex) by band\n{wide}")
            flagged = {c: {s_: m["definition"] for s_, m in r["meta"].items()
                           if m["definition"] != "any sex (full)"} for c, r in results.items()}
            flagged = {c: v for c, v in flagged.items() if v}
            if flagged:
                print("\nNOTE: these cycles used a NARROWER definition:", flagged)
            print(f"\nSaved results and run_log.json to {os.path.abspath(out_dir)}")
    return results


# =============================================================================
# Optional download helper
# =============================================================================
def download(cycle, data_dir="nsfg_data"):
    """Best-effort fetch from the CDC FTP site. Setup-file names vary by cycle, so several
    candidates are tried; anything not found is reported for manual download."""
    cycle = normalize_cycle(cycle)
    cfg = CYCLES[cycle]
    os.makedirs(data_dir, exist_ok=True)
    if cfg["kind"] == "fwf":
        wanted = [[FTP_OLD + cfg["fem"]], [FTP_OLD + cfg["male"]],
                  [FTP_OLD + "stata/" + n for n in cfg["fem_setup"]],
                  [FTP_OLD + "stata/" + n for n in cfg["male_setup"]]]
    else:
        wanted = [cfg["fem_urls"], cfg["male_urls"]]
    for urls in wanted:
        for url in urls:
            dest = os.path.join(data_dir, url.rsplit("/", 1)[1])
            if os.path.exists(dest):
                print(f"exists  {dest}")
                break
            try:
                urllib.request.urlretrieve(url, dest)
                print(f"got     {url}")
                break
            except Exception:
                continue
        else:
            print(f"MISSING could not fetch any of: {[u.rsplit('/', 1)[1] for u in urls]} -- "
                  f"download it manually from {urls[0].rsplit('/', 1)[0]}/")


# =============================================================================
if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--cycles", nargs="+", default=["all"])
    ap.add_argument("--data-dir", default="nsfg_data")
    ap.add_argument("--out", default="nsfg_results")
    ap.add_argument("--max-age", type=int, help="e.g. 44 to put every cycle on 15-44")
    ap.add_argument("--download", nargs="+", metavar="CYCLE")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    if a.list:
        for k, c in CYCLES.items():
            files = f"{c['fem']}, {c['male']} + .dct setups" if c["kind"] == "fwf" \
                else "female + male PUF .sas7bdat or .csv"
            print(f"{k:10s} ages {c['ages'][0]}-{c['ages'][1]}  weight {c['weight']:13s} {files}")
        sys.exit()
    if a.download:
        for c in (CYCLES if a.download == ["all"] else a.download):
            download(c, a.data_dir)
        sys.exit()
    run_all(a.cycles, a.data_dir, a.out, a.max_age)

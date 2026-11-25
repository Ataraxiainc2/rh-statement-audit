# rh-statement-audit

[Español](#español) · [English](#english) · [Créditos / Credits](#créditos--credits)

> Auditoría independiente del **enunciado** formal. No es una prueba, no es un informe de arbitraje y no
> está afiliada al autor ni a Anthropic. / An independent audit of the formal **statement**. It is not a proof,
> not a referee report, and not affiliated with the author or with Anthropic.

---

## Español

Auditoría del **enunciado** (no de la prueba) de `RiemannHypothesis` en Mathlib, en el entorno exacto de la
release de L. Alpöge del 20-nov-2026: Lean `v4.33.1` y Mathlib `0df444a3` (= tag `v4.33.1`).

Si el teorema final es el `RiemannHypothesis` de Mathlib, con axiomas estándar y aceptado por varios kernels,
solo quedan dos vías reales de fallo:
1. que el enunciado no signifique RH;
2. que el entorno de confianza esté alterado (fork de Mathlib, caché manipulada, homónimos).

Este repo ataca ambas con teoremas compilados y con chequeos automáticos.

### Contenido

| Fichero | Qué hace |
|---|---|
| `RhStatementAudit/Anchors.lean` | Teoremas de anclaje, todos demostrados: ζ = serie de Dirichlet (`HasSum`) en Re s > 1; ζ analítica en ℂ∖{1}; unicidad de la continuación; ζ(0) = −½, ζ(−1) = −1/12, ζ(2) = π²/6; ζ(1) ≠ 0; los ceros en Re ≤ 0 son exactamente −2(n+1); RH ⇔ forma de franja; RH ⇔ forma sin `s ≠ 1`; RH ⇔ forma **sin `riemannZeta`** (cualquier continuación analítica de la serie). |
| `RhStatementAudit/Eta.lean` | RH ⇔ RH para la **η de Dirichlet** como serie explícita emparejada Σₖ((2k+1)⁻ˢ − (2k+2)⁻ˢ), absolutamente convergente en Re s > 0 y sin `riemannZeta`. Incluye la explicación de por qué la serie alternada con `tsum` sería basura (= 0) en la franja. |
| `RhStatementAudit/Axioms.lean` | `#print axioms` de los 26 anclajes. |
| `scripts/check_axioms.py` | Falla si algún anclaje usa algo distinto de `propext`, `Classical.choice` y `Quot.sound`. |
| `scripts/check_pin.py` | Comprueba: toolchain `v4.33.1`; los 9 paquetes iguales a la release; SHA-256 de los ficheros de referencia iguales a los del archivo original; Mathlib upstream = tag `v4.33.1` y solo `lean-toolchain` difiere de `master`; checkout de Mathlib sin modificar; texto fuente de `def RiemannHypothesis`. |
| `scripts/scan_release.py` | Escaneo estático de la release: homónimos de las constantes del enunciado, `skipKernelTC`, imports de `Statements`/`Challenge`, origen de Mathlib en el `lakefile`. |
| `scripts/run_comparator.sh` | Receta para `comparator` completo con **nuestro** `Challenge.lean`. **No probada aquí** (necesita Linux y ~100 GB de RAM). |
| `.github/workflows/audit.yml` | CI con los jobs `pin`, `build` (compila y comprueba axiomas), `release-scan` y `comparator` (opcional, self-hosted). |
| `reference/` | `Statements.lean`, `Main.lean` y `lake-manifest.json` de la release, con SHA-256 verificado contra el archivo de alpo.ge. Además, `Challenge.lean` y `comparator.json` del montaje de Comparator (Deicyde / the-omega-institute), que **no** forman parte del archivo original. `Challenge.lean` importa solo `Mathlib`. |
| `ANALISIS.md` / `ANALYSIS.md` | Informe detallado del riesgo de enunciado (español / inglés). |
| `PETITION.md` | Propuesta (borrador, no enviada) para añadir estas equivalencias a Mathlib como tests de estabilidad. |

### Reproducir

```bash
lake exe cache get
lake build
python3 scripts/check_axioms.py
python3 scripts/check_pin.py --online
```

### Resultados (25-nov-2026, Windows 11, local)

* `lake exe cache get`: 8690/8690 ficheros, código 0.
* `lake build`: **8710/8710 jobs, build completed successfully**, 0 `sorry`.
* `check_axioms.py`: **PASS**, 26/26 anclajes con `[propext, Classical.choice, Quot.sound]`.
* `check_pin.py --online`: **PASS**. Hallazgo: el commit fijado **no es ancestro de `master`** de Mathlib
  (`diverged`). Es el tag oficial `v4.33.1`: un único commit «bump toolchain» que solo toca `lean-toolchain`.
* `scan_release.py` (los 175 187 `.lean` de la release, espejo tamnd `54f24d40`): **PASS**, 0 flags duros. Hay 2 homónimos `LFunction` en otros espacios de nombres, inocuos. Ver `ANALISIS.md` §8.
* **No ejecutado:** `comparator` completo (requiere ~100 GB de RAM). CI de GitHub (run 45687557153, ubuntu): `pin`, `build` (8710 jobs, axiomas PASS)
  y `release-scan` (175 187 ficheros, PASS) en **verde**. `comparator` se omitió, porque es opcional.

### Límites

* Los anclajes cubren `RiemannHypothesis` (ζ). No cubren los enunciados de L-funciones de Dirichlet (GRH) de
  la release.
* Se confía en las nociones básicas de Mathlib (`HasSum`, `cpow`, `AnalyticOnNhd`) y en el kernel.
* El job `build` usa la caché de Mathlib por defecto. Para no confiar en ella, lanza el workflow a mano con
  `from_source: true`.

---

## English

An audit of the **statement** (not the proof) of Mathlib's `RiemannHypothesis`, in the exact environment of
L. Alpöge's 2026-11-20 release: Lean `v4.33.1` and Mathlib `0df444a3` (= tag `v4.33.1`).

If the final theorem is Mathlib's `RiemannHypothesis`, with standard axioms and accepted by several kernels,
only two real failure routes remain:
1. the statement does not mean RH;
2. the trusted environment has been tampered with (Mathlib fork, tampered cache, homonyms).

This repository addresses both with compiled theorems and automated checks.

### Contents

| File | Purpose |
|---|---|
| `RhStatementAudit/Anchors.lean` | Anchor theorems, all proved: ζ = Dirichlet series (`HasSum`) on Re s > 1; ζ analytic on ℂ∖{1}; uniqueness of continuation; ζ(0) = −½, ζ(−1) = −1/12, ζ(2) = π²/6; ζ(1) ≠ 0; zeros in Re ≤ 0 are exactly −2(n+1); RH ⇔ strip form; RH ⇔ form without `s ≠ 1`; RH ⇔ a **`riemannZeta`-free** form (any analytic continuation of the series). |
| `RhStatementAudit/Eta.lean` | RH ⇔ RH for **Dirichlet's η** as the explicit paired series Σₖ((2k+1)⁻ˢ − (2k+2)⁻ˢ), absolutely convergent on Re s > 0, with no `riemannZeta`. Explains why the alternating series written with `tsum` would be junk (= 0) on the strip. |
| `RhStatementAudit/Axioms.lean` | `#print axioms` for all 26 anchors. |
| `scripts/check_axioms.py` | Fails unless every anchor uses only `propext`, `Classical.choice` and `Quot.sound`. |
| `scripts/check_pin.py` | Checks: toolchain `v4.33.1`; all 9 packages identical to the release; reference SHA-256 equal to the original archive; Mathlib = upstream tag `v4.33.1`, differing from `master` only in `lean-toolchain`; clean Mathlib checkout; source text of `def RiemannHypothesis`. |
| `scripts/scan_release.py` | Static scan of the release: homonyms of the statement's constants, `skipKernelTC`, imports of `Statements`/`Challenge`, Mathlib origin in the lakefile. |
| `scripts/run_comparator.sh` | Recipe for a full `comparator` run with **our own** `Challenge.lean`. **Untested here** (needs Linux and ~100 GB RAM). |
| `.github/workflows/audit.yml` | CI with jobs `pin`, `build` (compile + axiom check), `release-scan`, and `comparator` (optional, self-hosted). |
| `reference/` | The release's `Statements.lean`, `Main.lean` and `lake-manifest.json`, SHA-256-checked against the alpo.ge archive. Also `Challenge.lean` and `comparator.json` from the Comparator setup (Deicyde / the-omega-institute), which are **not** part of the original archive. `Challenge.lean` imports only `Mathlib`. |
| `ANALYSIS.md` | Detailed statement-risk report (English; Spanish original in `ANALISIS.md`). |
| `PETITION.md` | Proposal (draft, not submitted) to add these equivalences to Mathlib as statement-stability tests. |

### Reproduce

```bash
lake exe cache get
lake build
python3 scripts/check_axioms.py
python3 scripts/check_pin.py --online
```

### Results (2026-11-25, Windows 11, local)

* `lake exe cache get`: 8690/8690 files, exit code 0.
* `lake build`: **8710/8710 jobs, build completed successfully**, 0 `sorry`.
* `check_axioms.py`: **PASS**, all 26 anchors use `[propext, Classical.choice, Quot.sound]`.
* `check_pin.py --online`: **PASS**. Finding: the pinned commit is **not an ancestor of Mathlib `master`**
  (`diverged`). It is the official tag `v4.33.1`: one "bump toolchain" commit that only touches
  `lean-toolchain`.
* `scan_release.py` (all 175,187 release `.lean` files, tamnd mirror `54f24d40`): **PASS**, 0 hard flags. There are 2 harmless `LFunction` homonyms in other namespaces. See `ANALYSIS.md` §8.
* **Not run:** the full `comparator` (needs ~100 GB RAM). GitHub CI (run 45687557153, ubuntu): `pin`, `build` (8710 jobs, axioms PASS) and
  `release-scan` (175,187 files, PASS) all **green**; `comparator` skipped (optional).

### Limits

* The anchors cover `RiemannHypothesis` (ζ). They do not cover the release's Dirichlet L-function (GRH)
  statements.
* Mathlib's basic notions (`HasSum`, `cpow`, `AnalyticOnNhd`) and the kernel are trusted.
* The `build` job uses the Mathlib cache by default. To avoid trusting it, dispatch the workflow manually with
  `from_source: true`.

---

## Créditos / Credits

**La prueba / The proof.** Levent Alpöge (Anthropic; Junior Fellow, Harvard Society of Fellows), anunciada el
20-nov-2026 en la nota de cuatro páginas <https://alpo.ge/remark.pdf>, escrita, según el anuncio, trabajando
con Claude. La prueba se publicó solo como formalización en Lean, en el archivo `lean.tar.gz` (partes en
alpo.ge), SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
/ Announced on 2026-11-20 in the four-page note above, written, per the announcement, working with Claude.
The proof was released only as a Lean formalization (archive and hash as above).

**Lo que usa este repo / What this repo builds on.**
* Mathlib (`v4.33.1`): definiciones y lemas de ζ de D. Loeffler y otros. / ζ definitions and lemmas by
  D. Loeffler et al.
* `reference/Challenge.lean` y `comparator.json`: montaje de Comparator de Deicyde / the-omega-institute.
  / Comparator setup by Deicyde / the-omega-institute.
* Hashes por fichero del archivo / per-file archive hashes: tamnd/riemann-lean.
* `leanprover/comparator` (Lean FRO).
* Las equivalencias de franja y de caracterización ya las había enunciado C. Toledo (cert-machine,
  21-nov-2026) en el mismo pin. Este repo las reproduce de forma independiente y añade la forma con η, la
  exactitud de los ceros triviales y los chequeos de entorno. / The strip-form and characterization
  equivalences were stated earlier by C. Toledo (cert-machine, 2026-11-21) at the same pin. This repo
  reproduces them independently and adds the η form, exactness of the trivial zeros, and the environment
  checks.

**Transparencia / Transparency.** Este repositorio se preparó con ayuda de IA (Claude Code), bajo la
dirección y la responsabilidad de su propietario. Todo lo que afirma está respaldado por código que compila
(`lake build`, CI) o por fuentes enlazadas. / This repository was prepared with AI assistance (Claude Code),
under the direction and responsibility of its owner. Every claim is backed by compiling code (`lake build`,
CI) or by linked sources.

**Licencia / License.** Apache-2.0 (como Mathlib / like Mathlib). Los ficheros de `reference/` pertenecen a
sus autores. / Files in `reference/` belong to their authors.

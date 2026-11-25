# Análisis del riesgo de enunciado: `RiemannHypothesis` en la release de Alpöge

> Prueba anunciada por **Levent Alpöge** (Anthropic; Junior Fellow, Harvard Society of Fellows) el 20-nov-2026 en <https://alpo.ge/remark.pdf>, escrita, según el anuncio, trabajando con Claude. Este informe es una auditoría independiente del **enunciado**, no de la prueba, y no está afiliado al autor. Se preparó con ayuda de IA (Claude Code).

**Fecha:** 25-nov-2026 · **Entorno verificado:** Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
(= tag oficial `v4.33.1` de Mathlib), el mismo que fija el `lake-manifest.json` de la release (SHA-256
`fee57ee9…4774`, idéntico al del archivo `lean.tar.gz` de alpo.ge según el manifiesto por fichero de
tamnd/riemann-lean).

Todas las citas de código de este informe se han leído del **código fuente de Mathlib en ese commit**
(clon local en `rh-statement-audit/.lake/packages/mathlib`, `HEAD = 0df444a3`, árbol limpio), no de memoria.
Las afirmaciones marcadas **[Lean]** están demostradas en `rh-statement-audit/RhStatementAudit/*.lean`,
compiladas con `lake build` (8710/8710 jobs OK), y usan solo los axiomas `propext`, `Classical.choice` y `Quot.sound`.

---

## 0. Veredicto

La afirmación analizada es:

> «El enunciado no es el que creemos. Es el riesgo residual principal. Mathlib define RiemannHypothesis como: todo
> cero de riemannZeta que no sea trivial y con s ≠ 1 tiene parte real 1/2. Si esa definición o la de riemannZeta
> tuviera un fallo sutil, se habría probado otra cosa. Este riesgo es bajo: la definición existía y estaba revisada
> antes, y Toledo probó en Lean que equivale a la forma de libro.»

| Parte de la afirmación | Valoración |
|---|---|
| Paráfrasis de la definición | **Correcta**, aunque imprecisa en un punto: «no trivial» significa exactamente «no de la forma −2(n+1), n ∈ ℕ». No se usa ningún predicado de «trivialidad» aparte. |
| «Si la definición tuviera un fallo sutil, se habría probado otra cosa» | **Correcta.** Es la única vía de fallo que sobrevive si el kernel es sólido y los axiomas son los estándar. |
| «Es el riesgo residual principal» | **Matizable.** Entre los riesgos *semánticos* sí es el principal. Pero, una vez se compilan teoremas de anclaje como los de este repo, ese riesgo queda **comprobado mecánicamente**. Lo que queda como riesgo práctico principal es la **integridad del entorno de confianza**: que la Mathlib usada sea la upstream, sin tocar, y que la caché `.olean` sea fiable. `comparator` **no cubre eso por diseño** (§6). |
| «La definición existía y estaba revisada antes» | **Correcta y verificable.** `def RiemannHypothesis` entró en Mathlib 4 el 29-jun-2023 (port de mathlib3, X. Roblot, #5556). Se reescribió sobre Hurwitz el 31-may-2024 (D. Loeffler, #13273). Son casi 2,5 años de uso público antes de la release, y la cadena de definiciones de ζ tiene ~1,5 años en su forma actual. |
| «Toledo probó en Lean que equivale a la forma de libro» | **Existe, pero no lo he compilado.** Sus ficheros (`cert-machine/instruments/alpoge-grh/spec/{Spec,Textbook}.lean`) enuncian, en el mismo pin, la forma de franja y una caracterización de ζ libre de `riemannZeta`. Su informe deja dos chequeos del enunciado sin cerrar: *Comparator* se detuvo a las 53 h sin veredicto, y la prueba de errores plantados quedó «refused». **Este repo reproduce esas equivalencias de forma independiente y las amplía**: forma con la η explícita, conjunto exacto de ceros triviales y redundancia de `s ≠ 1`. |
| «Este riesgo es bajo» | **Correcto, pero la calificación se queda corta en un sentido y es engañosa en otro** (§7). Para el *significado* del enunciado, el riesgo es **muy bajo** y ahora está comprobado en Lean. Pero «bajo» invita a pensar que el riesgo restante está en la definición, cuando en realidad está en el **entorno**: pin de Mathlib, caché y toolchain. |

---

## 1. Definición exacta y cadena de definiciones (código fuente, commit `0df444a3`)

### 1.1 `RiemannHypothesis` — `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:183-186`

```lean
/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
@[wikidata Q205966]
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

* Los binders anónimos `(_ : P)` son implicaciones. El `n + 1` se elabora como `(↑n + 1 : ℂ)`. El `1 / 2`
  se elabora en `ℝ`, porque `s.re : ℝ`, así que vale 0,5 y no la división natural `1/2 = 0`.
  **[Lean]** `riemannHypothesis_unfold` muestra por `Iff.rfl` que la definición coincide carácter a carácter
  con el `RiemannZetaZerosOnLine` del `Statements.lean` de la release. Además, el `Main.lean` de la release
  cierra `riemannHypothesis` y `riemannZeta_eq_zero_re` con el mismo término `rhOfAll`, lo que confirma la
  igualdad definicional.

### 1.2 `riemannZeta` y su cadena

| Constante | Definición (fichero:línea) |
|---|---|
| `riemannZeta` | `def riemannZeta := hurwitzZetaEven 0` — `RiemannZeta.lean:121` |
| `hurwitzZetaEven a` | `Function.update (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s) 0 (if a = 0 then -1 / 2 else 0)` — `HurwitzZetaEven.lean:583-585` |
| `completedHurwitzZetaEven a s` | `((hurwitzEvenFEPair a).Λ (s / 2)) / 2` — `HurwitzZetaEven.lean:297` |
| `hurwitzEvenFEPair a : WeakFEPair ℂ` | `f := ofReal ∘ evenKernel a`, `g := ofReal ∘ cosKernel a`, `k := 1/2`, `ε := 1`, `f₀ := if a = 0 then 1 else 0`, `g₀ := 1` — `HurwitzZetaEven.lean:254-272` |
| `WeakFEPair.Λ s` | `P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀` — `AbstractFuncEq.lean:379` |
| `WeakFEPair.Λ₀` | `mellin P.f_modif` — `AbstractFuncEq.lean:376`. `f_modif` resta a `f` sus asíntotas en 0 y ∞ (`:247`). |
| `mellin f s` | `∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t` — `Analysis/MellinTransform.lean` |
| `evenKernel a x` | levantamiento a `UnitAddCircle` de `ξ ↦ rexp (-π ξ² x) · re (jacobiTheta₂ (ξ I x) (I x))` (`@[irreducible]`) — `HurwitzZetaEven.lean:63-75` |
| `jacobiTheta₂ z τ` | `∑' n : ℤ, cexp (2π i n z + π i n² τ)` — `JacobiTheta/TwoVariable.lean:45,251` |
| `Gammaℝ s` | `π ^ (-s / 2) * Gamma (s / 2)` — `Gamma/Deligne.lean:43` |
| `Complex.Gamma s` | `GammaAux ⌊1 - s.re⌋₊ s` (integral de Euler más recurrencia; `@[irreducible]`) — `Gamma/Basic.lean:287` |
| `cpow` | `x ^ y = if x = 0 then (if y = 0 then 1 else 0) else exp (log x * y)` — `Pow/Complex.lean:35` |

Es la construcción clásica de Riemann (vía θ y Mellin): Λ(s) = π^{-s/2} Γ(s/2) ζ(s), con los polos de Λ
en 0 y 1 sacados explícitamente mediante `f₀`, `g₀`.

---

## 2. Valores «basura» (junk values)

Mathlib totaliza las funciones parciales: `x / 0 = 0`, `Γ(−n) = 0` (`Complex.Gamma_neg_nat_eq_zero`,
`Gamma/Basic.lean:344`), y `tsum` de una familia no sumable vale `0`. Hay tres puntos en los que una
convención podría «fabricar» o «borrar» ceros:

### 2.1 `s = 1` (el polo)
* El valor que da la definición en `s = 1` es `ζ(1) = (γ − log 4π)/2` (`riemannZeta_one`, `ZetaAsymp.lean:418`).
  Es ≠ 0 (`riemannZeta_one_ne_zero`, `:441`).
* Consecuencia: la hipótesis `s ≠ 1` en `RiemannHypothesis` es **redundante**. Ni debilita ni refuerza.
  **[Lean]** `riemannHypothesis_iff_no_one`.
* Aunque `ζ(1)` fuera 0, como Re 1 ≠ 1/2, la hipótesis `s ≠ 1` estaría justo para impedir que RH fuese
  falsa por basura. Con `ζ(1) ≠ 0`, ni eso hace falta.

### 2.2 `s = 0` (parche explícito)
* `Γℝ(0) = Γ(0) = 0`, así que `Λ(0)/Γℝ(0)` sería basura `0`. Por eso `hurwitzZetaEven` **parchea** el
  valor en 0 con `Function.update … 0 (-1/2)`.
* ¿Es correcto el parche? Sí, y no hace falta fiarse: `differentiableAt_riemannZeta` (para todo `s ≠ 1`)
  implica continuidad en 0. Un valor parcheado erróneo haría ζ discontinua en 0 y ese teorema no compilaría.
  **[Lean]** `anchor_zeta_zero : riemannZeta 0 = -1/2`.

### 2.3 Ceros triviales `s = −2(n+1)` (división por cero «afortunada»)
* Aquí `Γℝ(−2(n+1)) = π^{n+1} Γ(−(n+1)) = 0` en Mathlib, así que **el valor de `riemannZeta` en los ceros
  triviales sale literalmente de `Λ(s)/0 = 0`**. Es una división por cero que coincide con el valor real.
* No es un problema: de nuevo, la diferenciabilidad en todo `s ≠ 1` obliga a que el valor sea el límite,
  que es el cero verdadero (Λ finito / Γℝ con polo).
* **Lección general:** cualquier valor puntual erróneo en `ℂ \ {1}` queda excluido por
  `differentiableOn_riemannZeta`. Por eso el anclaje de analiticidad no es decorativo: es el que mata los
  modos de fallo «valor basura en un punto aislado», por ejemplo un hipotético 0 espurio en ½ + 14,13 i o fuera
  de la recta.

### 2.4 `tsum` y la serie de Dirichlet
* `zeta_eq_tsum_one_div_nat_cpow` es una igualdad con `tsum`. Por sí sola podría ser «verdadera por basura»
  si la serie no fuese sumable. **[Lean]** `anchor_hasSum_dirichlet` la refuerza a `HasSum`, es decir,
  convergencia incondicional genuina, para `Re s > 1`.
* Para la η de Dirichlet es crítico (§5): la serie alternada solo converge **condicionalmente** en
  `0 < Re s ≤ 1`, de modo que `∑' n, (-1)^n/(n+1)^s` **vale 0 en toda la franja crítica**. Un «RH vía η»
  escrito ingenuamente con `tsum` sería un enunciado falso sobre basura. Por eso usamos la forma emparejada,
  que converge absolutamente.

---

## 3. Ceros triviales: ¿se excluye exactamente lo que hay que excluir?

El conjunto excluido es `T = {−2(n+1) : n ∈ ℕ} = {−2, −4, −6, …}`.

* Si se excluyera **de más**, RH se debilitaría. Por ejemplo con un `ℤ` en lugar de `ℕ`, o con una resta
  truncada en `ℕ`.
* Si se excluyera **de menos**, RH sería falsa, porque los ceros triviales tienen Re ≠ ½. En ese caso una
  «prueba» indicaría inconsistencia.
* **[Lean]** `anchor_trivial_zeros_exact`: en `Re s ≤ 0`, `ζ(s) = 0 ↔ s ∈ T`, exactamente. La demostración
  (`riemannZeta_ne_zero_of_re_nonpos`) usa la ecuación funcional `riemannZeta_one_sub`, la no anulación en
  `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`) y `Γ ≠ 0`. Así solo puede anularse cos(πw/2), lo que da los
  impares, es decir `s ∈ −2ℕ`. El caso `s = 0` cae fuera porque `ζ(0) = −½`.
* Nota: `riemannZeta_ne_zero_of_one_le_re` (`Nonvanishing.lean:411`) **no** exige `s ≠ 1`, precisamente
  porque la basura en 1 es no nula. Su docstring lo dice explícitamente.

---

## 4. Convención de `cpow`

`x ^ y = if x = 0 then (if y = 0 then 1 else 0) else exp (log x * y)`, con `log` principal
(arg ∈ (−π, π]).

* Para `x = n > 0` real, `log n ∈ ℝ`, así que `n^s = e^{s log n}`: es la convención estándar.
  No hay ambigüedad de rama en la serie.
* La única basura es `0^s = 0` (para `s ≠ 0`). En `∑_{n≥0} 1/n^s` el término `n = 0` vale `1/0 = 0`:
  es inofensivo. Mathlib da además la forma `n + 1` (`zeta_eq_tsum_one_div_nat_add_one_cpow`, cuyo
  docstring dice que es «to avoid relying on mathlib's conventions for `0 ^ s`»). Nuestros anclajes usan la
  forma `n + 1`.
* **[Lean]** `cpow_convention` fija la definición por `rfl`. Si cambiara upstream, el anclaje fallaría.

---

## 5. Qué lema descarta cada modo de fallo

| Modo de fallo hipotético | Efecto | Lo descarta |
|---|---|---|
| `riemannZeta` no es ζ en `Re s > 1` | se probaría RH para otra función | `zeta_eq_tsum_one_div_nat_cpow` / **[Lean]** `anchor_hasSum_dirichlet` (con `HasSum`), `riemannZeta_two = π²/6` |
| Continuación «equivocada» (otra función que coincide en Re > 1) | RH sobre otra función | `differentiableAt_riemannZeta` (s ≠ 1) + principio de identidad: **[Lean]** `anchor_unique` (cualquier `f` analítica en `ℂ\{1}` con esa serie coincide con `riemannZeta`) |
| Valor basura en un punto aislado (parches, `x/0`) | cero espurio o borrado | diferenciabilidad en todo `s ≠ 1` (§2.2–2.3); **[Lean]** `anchor_zeta_zero`, `anchor_zeta_neg_one = −1/12` |
| Basura en `s = 1` | RH falsa o vacía según el valor | `riemannZeta_one_ne_zero`; **[Lean]** `riemannHypothesis_iff_no_one` |
| Conjunto de ceros triviales mal escrito | RH debilitada o falsa | `riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_le_re`; **[Lean]** `anchor_trivial_zeros_exact` |
| `1/2` elaborado en `ℕ` (= 0) | RH diría «Re s = 0» | elaboración en `ℝ` (tipo de `s.re`); **[Lean]** las equivalencias con la forma de franja y con η serían imposibles con Re = 0 |
| Cuantificadores o hipótesis mal anidados | otro enunciado | **[Lean]** `riemannHypothesis_unfold` (`Iff.rfl`), `riemannHypothesis_iff_strip` |
| Toda la cadena Hurwitz/Mellin/θ es incorrecta | RH sobre otra función | **[Lean]** `riemannHypothesis_iff_viaContinuation` y `riemannHypothesis_iff_viaEta`: RH ⇔ enunciados en los que **no aparece `riemannZeta`** |
| Ecuación funcional incorrecta | ζ no simétrica | `riemannZeta_one_sub`, `completedRiemannZeta_one_sub` (Λ(1−s) = Λ(s)) |

**Qué no cubren los anclajes:** las nociones básicas en las que se apoyan (`HasSum`, `cpow` sobre reales
positivos, `AnalyticOnNhd`, `re`, `ℂ`). Un error ahí sería un error «profundo» de Mathlib que afectaría a casi
todo. Tampoco cubren los **enunciados de L-funciones de Dirichlet** de la release
(`DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`, …). Para esos, el `Textbook.lean` de Toledo
plantea una caracterización análoga (`IsTextbookL`), que no he compilado.

---

## 6. Qué garantiza y qué no `comparator`

Leído del código de `leanprover/comparator` (`Comparator/Compare.lean`) y de su README:

**Garantiza**, bajo sus supuestos, para cada teorema de `theorem_names`:
1. El **enunciado** (nombre, tipo, niveles de universo) es idéntico en Challenge y Solution.
2. **Sí compara dependencias de forma transitiva.** `compareAt` mete en una worklist todas las constantes
   usadas en el tipo del teorema. `loop` exige que cada una tenga un `ConstantInfo` **idéntico**
   (`challengeConst != solutionConst → throw`), es decir, tipo **y cuerpo** de las definiciones, y añade
   recursivamente sus constantes (`runForUsedConsts`). Por tanto, una redefinición homónima de `riemannZeta`,
   `hurwitzZetaEven`, etc. **dentro del entorno de la Solution** no pasa.
3. La prueba usa solo `permitted_axioms` y la acepta el kernel, más los kernels externos opcionales
   (nanoda, con-leche, …).

**No garantiza:**
* **Que el entorno común sea el correcto.** Su supuesto 1 dice literalmente: *«The transitive closure of
  imports of `Challenge.lean` as well as `lakefile.toml`/`lakefile.lean` are controlled by you or
  trustworthy.»* Challenge y Solution se compilan con **los mismos paquetes** del `lakefile`. Si este fijara
  un **fork** de Mathlib, el Challenge se compilaría contra el fork y la comparación sería fork contra fork:
  **pasaría**. Lo mismo vale para una caché `.olean` manipulada (el README: *«acceptable … if you trust the
  cache»*).
* **Que el enunciado del Challenge signifique lo que creemos.** Eso es justo lo que hacen los anclajes.
* Sobre la noticia de que «el paso de build estaba stubbeado»: no he podido verificarla. Si el build se
  sustituye por un `.lake` precompilado, el README lo admite solo si ese `.lake` se obtuvo «without
  compromising your checking environment». La garantía pasa entonces a depender de la procedencia de los
  `.olean`.
* **Detalle de versiones a aclarar:** según su README, `comparator` se integró en el core como
  `lake comparator` en Lean **v4.35.0**. La release usa **v4.33.1**, así que las corridas sobre la release
  habrán usado el `comparator` standalone o un `lake` más nuevo sobre un toolchain viejo. Conviene que cada
  informe diga qué binario y qué versión usó.

**Cómo cierra este repo el hueco del entorno** (`scripts/check_pin.py`, en CI):
* `lean-toolchain` es `v4.33.1`.
* Los 9 paquetes del manifest (nombre, URL y rev) son idénticos a los de la release, y el SHA-256 del
  manifest coincide con el del archivo original.
* La URL de Mathlib es la upstream `leanprover-community/mathlib4`.
* El commit fijado es el **tag oficial `v4.33.1`** de Mathlib. Respecto a `master`, solo añade un commit
  que toca **únicamente `lean-toolchain`** («chore: bump toolchain to v4.33.1», merge-base `db584cd6`).
  Ojo: **no es ancestro de `master`** (la API de GitHub devuelve `diverged`). Es normal en los tags de
  versión de Mathlib, pero un chequeo ingenuo de «¿está en master?» fallaría. Así le pasó a la primera
  versión de mi script.
* El checkout local de Mathlib está en ese commit **sin modificaciones** (`git status --porcelain` vacío) y
  el texto fuente de `def RiemannHypothesis` es el esperado.

---

## 7. ¿Es «bajo» la calificación correcta?

**Mi calificación:**

1. **Riesgo de que el enunciado formal no signifique RH: muy bajo, y comprobado en Lean.** En el entorno
   fijado, `RiemannHypothesis` es equivalente, con prueba compilada y axiomas estándar, a:
   * la forma de franja `∀ s, 0 < Re s < 1 → ζ(s) = 0 → Re s = ½`;
   * la forma sin `s ≠ 1`;
   * una forma **sin `riemannZeta`**: para toda `f` analítica en `ℂ\{1}` con `f(s) = ∑ (n+1)^{-s}`
     (`HasSum`) en `Re s > 1`, sus ceros en la franja están en la recta;
   * una forma **sin `riemannZeta`** con la η de Dirichlet como serie explícita absolutamente convergente.

   Lo que queda es la corrección del kernel (mitigada por nanoda y con-leche) y la de las nociones básicas
   de Mathlib.
2. **Riesgo de entorno (fork, caché, toolchain): bajo, pero es el que de verdad queda, y `comparator` no lo
   cubre.** Para la release, el pin apunta al tag upstream `v4.33.1` (verificado), así que el riesgo de fork
   está cerrado. El de **caché**, no del todo: quien use `lake exe cache get` confía en los `.olean` de la
   caché de Mathlib. Recompilar Mathlib desde fuente (opción `from_source` del CI) o reproducir desde un
   export con un kernel externo lo cierra.
3. **Riesgo de homónimos en imports no confiables:** cerrado para el enunciado por la comparación transitiva
   de `comparator` y con-leche. Además, el `Challenge.lean` y el `Statements.lean` de la release importan
   **solo** `Mathlib`. El escáner estático (`scripts/scan_release.py`) no encuentra declaraciones homónimas
   de las constantes del enunciado (ver §8).

**Conclusión:** «bajo» es correcto en la dirección, pero el texto original mezcla dos cosas:
* el riesgo **semántico**, que ya no hay que estimar porque se ha comprobado mecánicamente;
* el riesgo **operativo** (procedencia del entorno), que es el residual real y que la frase original no
  menciona.

La formulación que propondría:

> «El enunciado formal es el correcto: en Mathlib `v4.33.1` está probado en Lean, con axiomas estándar, que
> `RiemannHypothesis` equivale a la forma de franja y a dos formas que no mencionan `riemannZeta`. Lo que
> queda es la confianza en el kernel y en el entorno: Mathlib upstream sin modificar y caché fiable.
> `comparator` asume ese entorno en lugar de comprobarlo, así que debe auditarse aparte.»

---

## 8. Escaneo estático de la release

`python3 -I scripts/scan_release.py <release>/lean` sobre el espejo `tamnd/riemann-lean`. Es un espejo
byte-exacto del archivo de alpo.ge, con manifiesto SHA-256 por fichero. Las tres piezas clave
(`Statements.lean`, `Main.lean`, `lake-manifest.json`) coinciden con los hashes del archivo original.

Ejecución local del 25-nov-2026, leyendo desde el almacén de objetos git del espejo, commit `54f24d40`:
**175 187 ficheros `.lean` escaneados en 48 s. RESULT: PASS**. Salida completa en `rh-statement-audit/reference/scan_release_result.txt`.

| Chequeo | Resultado |
|---|---|
| Declaraciones con nombre **exacto** de una constante del enunciado (`RiemannHypothesis`, `riemannZeta`, `HurwitzZeta.hurwitzZetaEven`, `…completedHurwitzZetaEven`, `Gammaℝ`, `DirichletCharacter.LFunction`), `_root_.…`, o dentro de `namespace DirichletCharacter`/`HurwitzZeta` | **0** |
| `debug.skipKernelTC` / `skipKernelTypeCheck` | **0** |
| Declaraciones `axiom` | **0** |
| `unsafe`, `@[implemented_by]`, `@[extern]` | **0** |
| `Statements.lean` importa solo `Mathlib` | sí |
| Fuentes git del `lakefile.toml` | solo `https://github.com/leanprover-community/mathlib4` |
| Homónimos en *otros* espacios de nombres (blando) | 2: `GodementJacquet.LFunction`, `HeckeCharacter.LFunction`. No afectan: el enunciado usa el nombre totalmente cualificado `DirichletCharacter.LFunction`, y la comparación transitiva de comparator/con-leche lo fija. |
| `export` (blando) | 38, ninguno de constantes del enunciado (son nombres internos, p. ej. `f3`, `Kpp`, `exists_meas`) |
| `run_cmd` (blando) | 5, todos en `BuildAid/D1–D5.lean`, del tipo `Lean.modifyEnv … LibrarySuggestions.nameDenyListExt.addEntry …`. Solo afectan a sugerencias de tácticas, no a declaraciones. |
| `elab` (blando) | 4: tácticas internas (`kexactB`, `kcopy`) y un comando que copia declaraciones. Lo que producen pasa por el kernel, y las reproducciones desde el export (leanchecker, nanoda, con-leche) lo revisan. Pueden fallar, pero no introducir pruebas falsas. |

Nota de proceso: el primer intento de escaneo **no era válido**. El checkout de Windows falló por rutas
demasiado largas y solo extrajo 626 ficheros. La primera versión del regex además daba falsos positivos con
`Gammaℝ_conj`, porque `\b` no funciona tras `ℝ`. Ambas cosas están corregidas en la versión del script que
está en el repo.

El escaneo es **heurístico** (expresiones regulares sobre el fuente). No sustituye a la comparación
transitiva de `comparator` o con-leche, que trabaja sobre el entorno elaborado.

---

## 9. Fuentes

* Mathlib `0df444a3` (tag `v4.33.1`): `Mathlib/NumberTheory/LSeries/{RiemannZeta,HurwitzZetaEven,AbstractFuncEq,Nonvanishing}.lean`, `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`, `Mathlib/Analysis/SpecialFunctions/{Gamma/Basic,Gamma/Deligne,Pow/Complex}.lean`, `Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`, `Mathlib/Analysis/MellinTransform.lean`.
* Release: espejos [the-omega-institute/riemann-hypothesis](https://github.com/the-omega-institute/riemann-hypothesis), [CocoSgt/riemann-hypothesis-lean](https://github.com/CocoSgt/riemann-hypothesis-lean), [tamnd/riemann-lean](https://github.com/tamnd/riemann-lean) (hashes por fichero); [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) (`main` ya usa `v4.37.0-rc1`, **no** es el pin original).
* `comparator`: [leanprover/comparator](https://github.com/leanprover/comparator) (`README.md`, `Comparator/Compare.lean`).
* Toledo: [informe](https://carlostoledo.co/reports/alpoge-grh.html), [Spec.lean](https://github.com/carlostoledo1891/cert-machine/blob/main/instruments/alpoge-grh/spec/Spec.lean), [Textbook.lean](https://github.com/carlostoledo1891/cert-machine/blob/main/instruments/alpoge-grh/spec/Textbook.lean).
* Estado de verificaciones: [nasqret/riemann-rev](https://github.com/nasqret/riemann-rev).

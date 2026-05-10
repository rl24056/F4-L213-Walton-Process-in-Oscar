############################################################
# F4_L2_13_char7_hybrid_torus_normaliser_steps21_to26.jl
#
# One-piece GitHub / copy-paste script.
#
# Purpose:
#   Steps 21--25:
#     Work inside the hybrid torus-normaliser model
#
#         (Z/13Z)^4 x (Z/6Z)^4 . W(F4)
#
#     for the L2(13) < F4 characteristic-7 Walton-style search.
#
#     The script varies the torus part of f, tests Weyl-level
#     Bruhat obstructions, confirms that the only Weyl-compatible
#     candidate is the normalising/internal involution f^3, and
#     concludes that the current hybrid model is exhausted.
#
#   Step 26:
#     Writes and optionally runs a GAP script which records the
#     abstract PSL2(13) Bruhat fingerprint.  This distinguishes
#     the internal involution f^3 from the genuine external Bruhat
#     involution t.
#
# How to run:
#   In a fresh Julia / OSCAR session:
#
#       julia F4_L2_13_char7_hybrid_torus_normaliser_steps21_to26.jl
#
#   or paste the whole file after starting Julia.
#
# Notes:
#   - Steps 21--25 are Julia code.
#   - Step 26 is GAP code embedded as a raw string.  The Julia script
#     writes it to:
#
#       Step26_Abstract_PSL2_13_Bruhat_Fingerprint.g
#
#     and tries to run it if the command `gap` is available.
############################################################

using Oscar
using LinearAlgebra
using Random

Random.seed!(510)

println("============================================================")
println("F4 L2(13) CHAR 7 HYBRID TORUS-NORMALISER")
println("STEPS 21--26 COMBINED SCRIPT")
println("============================================================")

############################################################
# GLOBAL PARAMETERS
############################################################

# These were the only productive Weyl-involution indices from Step 20.
PRODUCTIVE_WIS = [1, 4, 5, 6, 7, 15, 46, 49]

# To keep the first run controlled, store at most this many trace -4 t's
# for each productive Weyl part.
#
# If Step 21 finds nothing and you still want a brute-force check,
# increase this to 10000 or 30000.
MAX_T_PER_W = 3000

# Number of f torus parts to test.
# There are 6^4 = 1296 total.
MAX_F_TO_TEST = 1296

# Stop after this many Bruhat hits in Step 21.
STOP_AFTER_HITS = 20

# Subgroup closure limit for <g,f,t>.
# PSL2(13) has order 1092, so 20000 is more than enough.
MAX_SUBGROUP_SIZE = 20000

############################################################
# BASIC MODULAR HELPERS
############################################################

function ModVec(v, m)
    return [mod(x, m) for x in v]
end

function Zero4()
    return [0, 0, 0, 0]
end

function I4()
    return Matrix{Int}(I, 4, 4)
end

function RowTimesMat(v, M)
    return [sum(v[i] * M[i,j] for i in 1:4) for j in 1:4]
end

function MatKey(M)
    return join([string(x) for x in vec(M)], ",")
end

function MatPow(M, n)
    P = I4()
    for i in 1:n
        P = P * M
    end
    return P
end

function MatOrder(M; limit=200)
    P = I4()
    for n in 1:limit
        P = P * M
        if P == I4()
            return n
        end
    end
    return 0
end

############################################################
# F4 ROOTS IN SIMPLE-ROOT COORDINATES
############################################################

function F4_EToSimple(v)
    x1, x2, x3, x4 = v

    c4 = 2*x1
    c1 = x2 + x1
    c2 = x3 + x2 + 2*x1
    c3 = x4 + x3 + x2 + 3*x1

    return [Int(c1), Int(c2), Int(c3), Int(c4)]
end

function PushUniqueRoot!(roots, r)
    if !(r in roots)
        push!(roots, r)
    end
end

function F4RootListSimple()
    rootsE = Vector{Vector{Rational{Int}}}()

    # roots +/- e_i
    for i in 1:4
        for s in [-1, 1]
            v = [0//1, 0//1, 0//1, 0//1]
            v[i] = s//1
            push!(rootsE, v)
        end
    end

    # roots +/- e_i +/- e_j
    for i in 1:4
        for j in (i+1):4
            for s in [-1, 1]
                for t in [-1, 1]
                    v = [0//1, 0//1, 0//1, 0//1]
                    v[i] = s//1
                    v[j] = t//1
                    push!(rootsE, v)
                end
            end
        end
    end

    # roots 1/2( +/- e1 +/- e2 +/- e3 +/- e4 )
    for s in Iterators.product([-1,1], [-1,1], [-1,1], [-1,1])
        v = [s[1]//2, s[2]//2, s[3]//2, s[4]//2]
        push!(rootsE, v)
    end

    rootsS = Vector{Vector{Int}}()
    for r in rootsE
        PushUniqueRoot!(rootsS, F4_EToSimple(r))
    end

    return rootsS
end

F4Roots = F4RootListSimple()

println("Number of F4 roots = ", length(F4Roots))

############################################################
# WEYL GROUP W(F4)
############################################################

CartanF4 = [
     2 -1  0  0;
    -1  2 -2  0;
     0 -1  2 -1;
     0  0 -1  2
]

function SimpleReflection(i)
    S = I4()
    for j in 1:4
        S[i,j] -= CartanF4[j,i]
    end
    return S
end

SimpleRefs = [SimpleReflection(i) for i in 1:4]

function GenerateWeylGroupF4()
    W = Matrix{Int}[]
    seen = Set{String}()

    Q = Matrix{Int}[I4()]
    push!(seen, MatKey(I4()))

    while !isempty(Q)
        M = popfirst!(Q)
        push!(W, M)

        for s in SimpleRefs
            N = M * s
            k = MatKey(N)

            if !(k in seen)
                push!(seen, k)
                push!(Q, N)
            end
        end
    end

    return W
end

W = GenerateWeylGroupF4()

println("Weyl group size = ", length(W))

############################################################
# HYBRID TORUS-NORMALISER ELEMENT
#
#   x = (u13, a6, w)
#
# with:
#   u13 in (Z/13Z)^4
#   a6  in (Z/6Z)^4
#   w   in W(F4)
############################################################

function Elem(u13, a6, w)
    return (
        u13 = ModVec(u13, 13),
        a6  = ModVec(a6, 6),
        w   = copy(w)
    )
end

function HId()
    return Elem(Zero4(), Zero4(), I4())
end

function HMul(x, y)
    u = ModVec(x.u13 .+ RowTimesMat(y.u13, x.w), 13)
    a = ModVec(x.a6  .+ RowTimesMat(y.a6,  x.w), 6)
    w = x.w * y.w
    return Elem(u, a, w)
end

function HPow(x, n)
    p = HId()
    for i in 1:n
        p = HMul(p, x)
    end
    return p
end

function HIsIdentity(x)
    return x.u13 == Zero4() && x.a6 == Zero4() && x.w == I4()
end

function ElemKey(x)
    return join(vcat(x.u13, x.a6, vec(x.w)), ",")
end

function HEqual(x, y)
    return ElemKey(x) == ElemKey(y)
end

function HOrder(x; limit=500)
    p = HId()
    for n in 1:limit
        p = HMul(p, x)
        if HIsIdentity(p)
            return n
        end
    end
    return 0
end

function IsOrder3Element(x)
    if HIsIdentity(x)
        return false
    end

    return HIsIdentity(HPow(x,3))
end

############################################################
# TRACE ON L(F4)
############################################################

function TraceElemInt(x)
    total = complex(float(tr(x.w)), 0.0)

    for r in F4Roots
        if RowTimesMat(r, x.w) == r
            e13 = sum(r[i] * x.u13[i] for i in 1:4) / 13
            e6  = sum(r[i] * x.a6[i]  for i in 1:4) / 6
            total += cis(2*pi*(e13 + e6))
        end
    end

    if abs(imag(total)) > 1.0e-6
        println("WARNING: trace has non-small imaginary part: ", total)
    end

    return round(Int, real(total))
end

############################################################
# ALL VECTORS MOD m
############################################################

function AllVectorsMod(m)
    vecs = Vector{Vector{Int}}()

    for a in 0:(m-1)
        for b in 0:(m-1)
            for c in 0:(m-1)
                for d in 0:(m-1)
                    push!(vecs, [a,b,c,d])
                end
            end
        end
    end

    return vecs
end

All13 = AllVectorsMod(13)
All6  = AllVectorsMod(6)

println("Prepared vectors:")
println("  |(Z/13Z)^4| = ", length(All13))
println("  |(Z/6Z)^4|  = ", length(All6))

############################################################
# INVOLUTION LIFT SOLUTIONS
#
# For t = (u,a,M), t^2 = 1 requires:
#   u + uM = 0 mod 13
#   a + aM = 0 mod 6
############################################################

function InvolutionSolutions(M, m, AllVecs)
    sols = Vector{Vector{Int}}()

    for v in AllVecs
        test = ModVec(v .+ RowTimesMat(v, M), m)

        if test == Zero4()
            push!(sols, v)
        end
    end

    return sols
end

############################################################
# RECONSTRUCT g AND CORRECTED wf
############################################################

gvec = [1, 1, 1, 1]

wf_candidates = Matrix{Int}[]

for M in W
    image = ModVec(RowTimesMat(gvec, M), 13)
    target = ModVec(10 .* gvec, 13)

    if image == target
        push!(wf_candidates, M)
    end
end

println("Number of Weyl elements sending gvec to 10*gvec mod 13 = ",
        length(wf_candidates))

if length(wf_candidates) == 0
    error("No corrected Weyl part wf found. Stop.")
end

wf = wf_candidates[1]

println("Chosen wf has order = ", MatOrder(wf))
println("Chosen wf has toral trace = ", tr(wf))
println("wf matrix = ")
display(wf)

g = Elem(gvec, Zero4(), I4())

println("Order(g) = ", HOrder(g))

############################################################
# BUILD ALL WEYL INVOLUTIONS
############################################################

involution_ws = Matrix{Int}[]

for M in W
    if MatOrder(M) == 2
        push!(involution_ws, M)
    end
end

println("Total Weyl involutions = ", length(involution_ws))

############################################################
# WEYL ACTION ON <g>
############################################################

function WeylNormalisesG(M, gvec)
    image = ModVec(RowTimesMat(gvec, M), 13)

    for k in 1:12
        if image == ModVec(k .* gvec, 13)
            return true
        end
    end

    return false
end

function WeylGExponent(M, gvec)
    image = ModVec(RowTimesMat(gvec, M), 13)

    for k in 1:12
        if image == ModVec(k .* gvec, 13)
            return k
        end
    end

    return 0
end

############################################################
# SUBGROUP HELPERS
############################################################

function PowersOfElement(x, maxpow)
    arr = Any[]

    for i in 0:maxpow
        push!(arr, HPow(x,i))
    end

    return arr
end

gPows = PowersOfElement(g, 12)

function GeneratedSubgroupElements(gens; MAX_SIZE = 50000)
    id = HId()

    elems = Any[id]
    seen = Set{String}([ElemKey(id)])
    frontier = Any[id]

    while !isempty(frontier)
        x = popfirst!(frontier)

        for gen in gens
            y = HMul(x, gen)
            ky = ElemKey(y)

            if !(ky in seen)
                push!(seen, ky)
                push!(elems, y)
                push!(frontier, y)

                if length(elems) > MAX_SIZE
                    return elems, false
                end
            end
        end
    end

    return elems, true
end

function GeneratedSubgroupSize(gens; MAX_SIZE = 20000)
    elems, completed = GeneratedSubgroupElements(gens; MAX_SIZE = MAX_SIZE)
    return length(elems), completed
end

function GeneratedSubgroupSizeFast(gens; MAX_SIZE = 50000)
    elems, completed = GeneratedSubgroupElements(gens; MAX_SIZE = MAX_SIZE)
    return length(elems), completed
end

############################################################
# STEP 21:
# VARY THE TORUS PART OF f AND SEARCH FOR BRUHAT-TYPE t
############################################################

println("============================================================")
println("STEP 21: VARY TORUS PART OF f AND SEARCH FOR t")
println("============================================================")

println("============================================================")
println("STEP 21A: WEYL-LEVEL BRUHAT PREFILTER")
println("============================================================")

GoodJByWI = Dict{Int, Vector{Int}}()

for wi in PRODUCTIVE_WIS
    M = involution_ws[wi]

    good_js = Int[]

    for j in 0:5
        N = MatPow(wf, j) * M
        ordN = MatOrder(N)

        if ordN == 1 || ordN == 3
            push!(good_js, j)
        end
    end

    GoodJByWI[wi] = good_js

    println("w_index = ", wi,
            " | tr(w) = ", tr(M),
            " | possible f-exponents j = ", good_js)
end

total_good_weyl = sum(length(GoodJByWI[wi]) for wi in PRODUCTIVE_WIS)

println("Total Weyl-level possible pairs (w_index, j) = ", total_good_weyl)

if total_good_weyl == 0
    println("No Weyl-level Bruhat possibilities among productive Step-20 Weyl parts.")
    println("This means varying the torus part of f cannot help inside this restricted Step-21 cache.")
end

println("============================================================")
println("STEP 21B: BUILD TRACE -4 t CANDIDATE CACHE")
println("============================================================")

function BuildTraceMinus4Cache(
    PRODUCTIVE_WIS,
    GoodJByWI;
    MAX_T_PER_W = 3000
)
    TCache = Dict{Int, Any}()

    total_cached = 0

    for wi in PRODUCTIVE_WIS
        good_js = GoodJByWI[wi]

        if length(good_js) == 0
            println("Skipping w_index ", wi, " because it has no Weyl-level Bruhat j.")
            continue
        end

        M = involution_ws[wi]

        Usol = InvolutionSolutions(M, 13, All13)
        Asol = InvolutionSolutions(M, 6, All6)

        println("Building cache for w_index ", wi,
                " | tr(w)=", tr(M),
                " | Usol=", length(Usol),
                " | Asol=", length(Asol),
                " | max store=", MAX_T_PER_W)

        candidates = Any[]
        checked = 0
        trace_hits = 0

        for u in Usol
            for a in Asol
                checked += 1

                t = Elem(u, a, M)

                if !HIsIdentity(HMul(t,t))
                    continue
                end

                if TraceElemInt(t) != -4
                    continue
                end

                trace_hits += 1

                if length(candidates) < MAX_T_PER_W
                    push!(candidates, (
                        t = t,
                        wi = wi,
                        w_trace = tr(M),
                        u13 = copy(u),
                        a6 = copy(a),
                        good_js = copy(good_js)
                    ))
                end
            end
        end

        TCache[wi] = candidates
        total_cached += length(candidates)

        println("  checked = ", checked)
        println("  total trace -4 hits for this w = ", trace_hits)
        println("  cached = ", length(candidates))
        println("------------------------------------------------------------")
    end

    println("Total cached trace -4 t candidates = ", total_cached)

    return TCache
end

TCache21 = BuildTraceMinus4Cache(
    PRODUCTIVE_WIS,
    GoodJByWI;
    MAX_T_PER_W = MAX_T_PER_W
)

function FindBruhatWitnessForF_Step21(fcur, t_rec)
    fPows = PowersOfElement(fcur, 5)

    for j in t_rec.good_js
        for i in 0:12
            b = HMul(gPows[i+1], fPows[j+1])
            x = HMul(b, t_rec.t)

            if IsOrder3Element(x)
                return true, i, j, b
            end
        end
    end

    return false, 0, 0, HId()
end

println("============================================================")
println("STEP 21C: VARY f AND SEARCH FOR BRUHAT t")
println("============================================================")

function RunVaryFSearch(
    All6,
    TCache21;
    MAX_F_TO_TEST = 1296,
    STOP_AFTER_HITS = 20,
    MAX_SUBGROUP_SIZE = 20000
)
    Hits = Any[]

    f_checked = 0
    f_valid = 0
    total_t_tests = 0

    for af in All6
        f_checked += 1

        if f_checked > MAX_F_TO_TEST
            break
        end

        fcur = Elem(Zero4(), af, wf)

        # Safety checks for f.
        if HOrder(fcur) != 6
            continue
        end

        if TraceElemInt(fcur) != 2
            continue
        end

        if TraceElemInt(HPow(fcur,2)) != -2
            continue
        end

        if TraceElemInt(HPow(fcur,3)) != -4
            continue
        end

        # Check action on g via Weyl part:
        # f*g*f^-1 should send g to g^10.
        if ModVec(RowTimesMat(gvec, fcur.w), 13) != ModVec(10 .* gvec, 13)
            continue
        end

        f_valid += 1

        if f_valid % 50 == 0
            println("Checked f candidates = ", f_checked,
                    " | valid f candidates = ", f_valid,
                    " | hits so far = ", length(Hits),
                    " | total t tests = ", total_t_tests)
        end

        for wi in sort(collect(keys(TCache21)))
            candidates = TCache21[wi]

            for t_rec in candidates
                total_t_tests += 1

                hit, i, j, b = FindBruhatWitnessForF_Step21(fcur, t_rec)

                if hit
                    subgroup_size, completed = GeneratedSubgroupSize(
                        [g, fcur, t_rec.t];
                        MAX_SIZE = MAX_SUBGROUP_SIZE
                    )

                    rec = (
                        f_a6 = copy(af),
                        t = t_rec.t,
                        t_w_index = t_rec.wi,
                        t_w_trace = t_rec.w_trace,
                        t_u13 = copy(t_rec.u13),
                        t_a6 = copy(t_rec.a6),
                        b_i = i,
                        b_j = j,
                        subgroup_size = subgroup_size,
                        subgroup_completed = completed
                    )

                    push!(Hits, rec)

                    println("============================================================")
                    println("BRUHAT HIT #", length(Hits))
                    println("  f torus part af = ", af)
                    println("  t w_index = ", t_rec.wi)
                    println("  t w_trace = ", t_rec.w_trace)
                    println("  t u13 = ", t_rec.u13)
                    println("  t a6  = ", t_rec.a6)
                    println("  b = g^", i, " * f^", j)
                    println("  Order(t) = ", HOrder(t_rec.t))
                    println("  Trace(t) = ", TraceElemInt(t_rec.t))
                    println("  Order(b*t) = ", HOrder(HMul(b, t_rec.t)))
                    println("  |<g,f,t>| = ", subgroup_size)
                    println("  subgroup closure completed? ", completed)

                    if subgroup_size == 1092
                        println("  SUCCESS: subgroup size is 1092, matching PSL2(13).")
                    end

                    println("============================================================")

                    if length(Hits) >= STOP_AFTER_HITS
                        println("Reached STOP_AFTER_HITS = ", STOP_AFTER_HITS)
                        println("Stopping search.")
                        return Hits
                    end
                end
            end
        end
    end

    println("============================================================")
    println("STEP 21C FINAL SUMMARY")
    println("============================================================")
    println("f candidates checked = ", f_checked)
    println("valid f candidates = ", f_valid)
    println("total cached t tests = ", total_t_tests)
    println("Bruhat hits found = ", length(Hits))

    return Hits
end

Hits21 = RunVaryFSearch(
    All6,
    TCache21;
    MAX_F_TO_TEST = MAX_F_TO_TEST,
    STOP_AFTER_HITS = STOP_AFTER_HITS,
    MAX_SUBGROUP_SIZE = MAX_SUBGROUP_SIZE
)

println("============================================================")
println("STORED STEP 21 HITS")
println("============================================================")

if length(Hits21) == 0
    println("No Bruhat hits found in this Step 21 run.")
    println("If the Weyl-level prefilter had possible pairs, then the next move is:")
    println("  increase MAX_T_PER_W and rerun, especially for productive w indices 46 and 49.")
    println("If the Weyl-level prefilter had no possible pairs, then this hybrid search is probably too small.")
else
    for i in 1:length(Hits21)
        rec = Hits21[i]

        println("Hit ", i)
        println("  f_a6 = ", rec.f_a6)
        println("  t_w_index = ", rec.t_w_index)
        println("  t_w_trace = ", rec.t_w_trace)
        println("  t_u13 = ", rec.t_u13)
        println("  t_a6  = ", rec.t_a6)
        println("  b = g^", rec.b_i, " * f^", rec.b_j)
        println("  |<g,f,t>| = ", rec.subgroup_size)
        println("  subgroup closure completed? ", rec.subgroup_completed)
        println("------------------------------------------------------------")
    end
end

println("============================================================")
println("END STEP 21")
println("============================================================")

############################################################
# STEP 22:
# EXHAUST THE WEYL-LEVEL BRUHAT OBSTRUCTION FOR ALL WEYL
# INVOLUTIONS, NOT ONLY THE PRODUCTIVE STEP-20 INDICES.
############################################################

println("============================================================")
println("STEP 22: ALL-WEYL BRUHAT OBSTRUCTION CHECK")
println("============================================================")

println("============================================================")
println("STEP 22A: ALL-WEYL BRUHAT PREFILTER")
println("============================================================")

WeylBruhatRows = Any[]
WeylBruhatIndices = Int[]

for wi in eachindex(involution_ws)
    M = involution_ws[wi]

    good_js = Int[]

    for j in 0:5
        N = MatPow(wf, j) * M
        ordN = MatOrder(N)

        if ordN == 1 || ordN == 3
            push!(good_js, j)
        end
    end

    if length(good_js) > 0
        push!(WeylBruhatIndices, wi)
    end

    push!(WeylBruhatRows, (
        w_index = wi,
        w_trace = tr(M),
        normalises_g = WeylNormalisesG(M, gvec),
        good_js = copy(good_js)
    ))
end

println("Number of Weyl involutions with some Bruhat-level j = ",
        length(WeylBruhatIndices))

println("------------------------------------------------------------")
println("Weyl involutions passing Bruhat-level prefilter:")
for row in WeylBruhatRows
    if length(row.good_js) > 0
        println("  w_index=", row.w_index,
                " | tr(w)=", row.w_trace,
                " | normalises <g>? ", row.normalises_g,
                " | good_js=", row.good_js)
    end
end

println("============================================================")
println("STEP 22B: TRACE -4 LIFT CHECK FOR WEYL-COMPATIBLE PARTS")
println("============================================================")

TraceBruhatCompatible = Any[]

total_weyl_compatible_checked = 0
total_trace_minus4_lifts = 0

for wi in WeylBruhatIndices
    M = involution_ws[wi]

    good_js = WeylBruhatRows[wi].good_js

    Usol = InvolutionSolutions(M, 13, All13)
    Asol = InvolutionSolutions(M, 6, All6)

    checked = 0
    trace_hits = 0
    examples = Any[]

    for u in Usol
        for a in Asol
            checked += 1
            total_weyl_compatible_checked += 1

            t = Elem(u, a, M)

            if !HIsIdentity(HMul(t,t))
                continue
            end

            if TraceElemInt(t) != -4
                continue
            end

            trace_hits += 1
            total_trace_minus4_lifts += 1

            if length(examples) < 5
                push!(examples, (
                    t = t,
                    u13 = copy(u),
                    a6 = copy(a)
                ))
            end
        end
    end

    push!(TraceBruhatCompatible, (
        w_index = wi,
        w_trace = tr(M),
        normalises_g = WeylNormalisesG(M, gvec),
        good_js = copy(good_js),
        Usol = length(Usol),
        Asol = length(Asol),
        checked = checked,
        trace_hits = trace_hits,
        examples = examples
    ))

    println("w_index=", wi,
            " | tr(w)=", tr(M),
            " | normalises <g>? ", WeylNormalisesG(M, gvec),
            " | good_js=", good_js,
            " | Usol=", length(Usol),
            " | Asol=", length(Asol),
            " | checked=", checked,
            " | trace -4 lifts=", trace_hits)
end

println("------------------------------------------------------------")
println("Total checked among Weyl-compatible parts = ",
        total_weyl_compatible_checked)
println("Total trace -4 lifts among Weyl-compatible parts = ",
        total_trace_minus4_lifts)

println("============================================================")
println("STEP 22C: FULL SEARCH ONLY IF NEEDED")
println("============================================================")

function FindBruhatWitnessForF_Step22(fcur, t, good_js)
    fPows = PowersOfElement(fcur, 5)

    for j in good_js
        for i in 0:12
            b = HMul(gPows[i+1], fPows[j+1])
            x = HMul(b, t)

            if IsOrder3Element(x)
                return true, i, j, b
            end
        end
    end

    return false, 0, 0, HId()
end

Hits22 = Any[]

if total_trace_minus4_lifts == 0
    println("No trace -4 lifts occur for any Weyl part that can satisfy")
    println("the necessary Weyl-level Bruhat condition.")
    println("")
    println("CONCLUSION:")
    println("Inside this hybrid torus-normaliser model, no element t can satisfy")
    println("simultaneously:")
    println("  Order(t)=2")
    println("  Trace(t)=-4")
    println("  Order(b*t)=3 for some b in <g,f>")
    println("even after varying the torus part of f.")
else
    println("Trace -4 Weyl-compatible lifts exist.")
    println("Proceeding to full search over all 1296 f torus parts.")

    # Build t records from examples only first.
    # If hits appear here, enlarge to full storage later.
    TRecords = Any[]

    for row in TraceBruhatCompatible
        if row.trace_hits > 0
            for ex in row.examples
                push!(TRecords, (
                    t = ex.t,
                    w_index = row.w_index,
                    w_trace = row.w_trace,
                    u13 = ex.u13,
                    a6 = ex.a6,
                    good_js = row.good_js
                ))
            end
        end
    end

    println("Number of example t records to test = ", length(TRecords))

    f_checked = 0
    f_valid = 0
    total_tests = 0

    for af in All6
        f_checked += 1

        fcur = Elem(Zero4(), af, wf)

        if HOrder(fcur) != 6
            continue
        end

        if TraceElemInt(fcur) != 2
            continue
        end

        if TraceElemInt(HPow(fcur,2)) != -2
            continue
        end

        if TraceElemInt(HPow(fcur,3)) != -4
            continue
        end

        f_valid += 1

        for trec in TRecords
            total_tests += 1

            hit, i, j, b = FindBruhatWitnessForF_Step22(fcur, trec.t, trec.good_js)

            if hit
                subgroup_size, completed = GeneratedSubgroupSize(
                    [g, fcur, trec.t];
                    MAX_SIZE = 20000
                )

                push!(Hits22, (
                    f_a6 = copy(af),
                    t_w_index = trec.w_index,
                    t_w_trace = trec.w_trace,
                    t_u13 = trec.u13,
                    t_a6 = trec.a6,
                    b_i = i,
                    b_j = j,
                    subgroup_size = subgroup_size,
                    subgroup_completed = completed
                ))

                println("============================================================")
                println("BRUHAT HIT #", length(Hits22))
                println("  f_a6 = ", af)
                println("  t_w_index = ", trec.w_index)
                println("  t_w_trace = ", trec.w_trace)
                println("  t_u13 = ", trec.u13)
                println("  t_a6  = ", trec.a6)
                println("  b = g^", i, " * f^", j)
                println("  Order(b*t) = ", HOrder(HMul(b, trec.t)))
                println("  |<g,f,t>| = ", subgroup_size)
                println("  subgroup closure completed? ", completed)

                if subgroup_size == 1092
                    println("  SUCCESS: subgroup size is 1092, matching PSL2(13).")
                end

                println("============================================================")
            end
        end
    end

    println("Full example-search finished.")
    println("f checked = ", f_checked)
    println("valid f = ", f_valid)
    println("total example t tests = ", total_tests)
    println("Bruhat hits = ", length(Hits22))
end

println("============================================================")
println("STEP 22 FINAL SUMMARY")
println("============================================================")

println("Total Weyl involutions = ", length(involution_ws))
println("Weyl involutions with Bruhat-level possible j = ",
        length(WeylBruhatIndices))
println("Total trace -4 lifts among Weyl-compatible Weyl parts = ",
        total_trace_minus4_lifts)
println("Bruhat hits found in optional full search = ", length(Hits22))

println("------------------------------------------------------------")
println("Interpretation:")
if length(WeylBruhatIndices) == 0
    println("No Weyl involution can even satisfy the necessary Weyl-level Bruhat condition.")
elseif total_trace_minus4_lifts == 0
    println("Some Weyl involutions satisfy the Weyl-level Bruhat condition,")
    println("but none of them has a trace -4 lift.")
    println("Therefore the hybrid torus-normaliser model is exhausted for this t-search.")
else
    println("There are trace -4 lifts with Weyl-level Bruhat compatibility.")
    println("Study Hits22 and then enlarge the stored t records if needed.")
end

println("============================================================")
println("END STEP 22")
println("============================================================")

############################################################
# STEP 23:
# FAST CORRECTED INTERPRETATION OF STEP 22
############################################################

println("============================================================")
println("STEP 23: FAST CORRECTED WEYL-LEVEL CONCLUSION")
println("============================================================")

AllWeylRows23 = Any[]

NormalisingBruhatRows23 = Any[]
NonNormalisingBruhatRows23 = Any[]

for wi in eachindex(involution_ws)
    M = involution_ws[wi]

    good_js = Int[]

    for j in 0:5
        N = MatPow(wf, j) * M
        ordN = MatOrder(N)

        if ordN == 1 || ordN == 3
            push!(good_js, j)
        end
    end

    normalises = WeylNormalisesG(M, gvec)
    exponent = WeylGExponent(M, gvec)

    row = (
        w_index = wi,
        w_trace = tr(M),
        normalises_g = normalises,
        g_exponent = exponent,
        good_js = copy(good_js)
    )

    push!(AllWeylRows23, row)

    if length(good_js) > 0
        if normalises
            push!(NormalisingBruhatRows23, row)
        else
            push!(NonNormalisingBruhatRows23, row)
        end
    end
end

println("Total Weyl involutions = ", length(involution_ws))
println("Weyl involutions satisfying necessary Bruhat Weyl condition and normalising <g> = ",
        length(NormalisingBruhatRows23))
println("Weyl involutions satisfying necessary Bruhat Weyl condition and NOT normalising <g> = ",
        length(NonNormalisingBruhatRows23))

println("------------------------------------------------------------")
println("Normalising Weyl-compatible rows:")
for row in NormalisingBruhatRows23
    println("  w_index = ", row.w_index,
            " | tr(w) = ", row.w_trace,
            " | action on <g>: g -> g^", row.g_exponent,
            " | good_js = ", row.good_js)
end

println("------------------------------------------------------------")
println("Non-normalising Weyl-compatible rows:")
if length(NonNormalisingBruhatRows23) == 0
    println("  None.")
else
    for row in NonNormalisingBruhatRows23
        println("  w_index = ", row.w_index,
                " | tr(w) = ", row.w_trace,
                " | good_js = ", row.good_js)
    end
end

println("============================================================")
println("STEP 23 CONCLUSION")
println("============================================================")

if length(NonNormalisingBruhatRows23) == 0
    println("No Weyl involution which moves <g> satisfies the necessary")
    println("Weyl-level Bruhat condition Order(wf^j * w_t) = 1 or 3.")
    println("")
    println("The only Weyl-compatible case normalises <g>.")
    println("Since f also normalises <g>, using such a t keeps <g,f,t>")
    println("inside the normaliser of <g>.")
    println("")
    println("Therefore this hybrid torus-normaliser model cannot contain")
    println("the PSL2(13)-type Bruhat t we need.")
    println("")
    println("This does NOT prove non-existence in genuine F4(7).")
    println("It means the current hybrid torus-normaliser search is exhausted.")
else
    println("There are non-normalising Weyl-compatible rows.")
    println("We should next test trace -4 lifts only for those rows.")
end

println("============================================================")
println("END STEP 23")
println("============================================================")

############################################################
# STEP 24:
# FINAL DIAGNOSTIC FOR THE ONLY WEYL-COMPATIBLE CANDIDATE
############################################################

println("============================================================")
println("STEP 24: FINAL NORMALISING-CANDIDATE DIAGNOSTIC")
println("============================================================")

# Build the first corrected f again:
#   f = ([0,0,0,0], [0,0,0,0], wf)

f0 = Elem(Zero4(), Zero4(), wf)

println("Order(g) = ", HOrder(g))
println("Order(f0) = ", HOrder(f0))
println("Trace(f0) = ", TraceElemInt(f0))
println("Trace(f0^2) = ", TraceElemInt(HPow(f0,2)))
println("Trace(f0^3) = ", TraceElemInt(HPow(f0,3)))

# Build B0 = <g,f0>

B0 = Any[]
B0Expr = String[]
seenB0 = Set{String}()

for i in 0:12
    for j in 0:5
        b = HMul(HPow(g,i), HPow(f0,j))
        k = ElemKey(b)

        if !(k in seenB0)
            push!(seenB0, k)
            push!(B0, b)
            push!(B0Expr, "g^$(i)*f^$(j)")
        end
    end
end

println("Size of B0 = <g,f0> = ", length(B0))

# The only Weyl-compatible candidate from Step 23.

w139 = involution_ws[139]
t0 = Elem(Zero4(), Zero4(), w139)

println("------------------------------------------------------------")
println("Testing the simple lift of w_index = 139")
println("Order(t0) = ", HOrder(t0))
println("Trace(t0) = ", TraceElemInt(t0))
println("Weyl trace of w139 = ", tr(w139))
println("Does w139 normalise <g>? ", WeylNormalisesG(w139, gvec))
println("Action exponent on <g>: g -> g^", WeylGExponent(w139, gvec))

println("------------------------------------------------------------")
println("Testing Order(b*t0)=3 for b in B0")

bruhat_count = 0
bruhat_examples = Any[]

for idx in eachindex(B0)
    x = HMul(B0[idx], t0)

    if IsOrder3Element(x)
        global bruhat_count += 1

        if length(bruhat_examples) < 20
            push!(bruhat_examples, (
                b_expr = B0Expr[idx],
                order_bt = HOrder(x)
            ))
        end
    end
end

println("Number of b in B0 with Order(b*t0)=3 = ", bruhat_count)

if bruhat_count > 0
    println("First examples:")
    for ex in bruhat_examples
        println("  b = ", ex.b_expr, " | Order(b*t0) = ", ex.order_bt)
    end
else
    println("No order-3 relation even for this simple lift.")
end

println("------------------------------------------------------------")
println("Computing size of <g,f0,t0>")

size_gft0, completed_gft0 = GeneratedSubgroupSizeFast(
    [g, f0, t0];
    MAX_SIZE = 50000
)

println("|<g,f0,t0>| = ", size_gft0)
println("Subgroup closure completed? ", completed_gft0)

if size_gft0 == 1092
    println("Unexpected: size is 1092.")
else
    println("As expected, this does not give PSL2(13).")
end

println("------------------------------------------------------------")
println("Checking whether generators normalise <g>")

println("f0 Weyl action exponent on <g>: g -> g^",
        WeylGExponent(f0.w, gvec))
println("t0 Weyl action exponent on <g>: g -> g^",
        WeylGExponent(t0.w, gvec))

if WeylGExponent(f0.w, gvec) != 0 && WeylGExponent(t0.w, gvec) != 0
    println("Both f0 and t0 normalise <g>.")
    println("Therefore <g,f0,t0> remains inside a normaliser of <g>.")
    println("This cannot be the full PSL2(13) Bruhat completion.")
else
    println("At least one generator does not normalise <g>.")
end

println("============================================================")
println("STEP 24 FINAL CONCLUSION")
println("============================================================")
println("The only Weyl-level Bruhat-compatible involution is normalising.")
println("This confirms that the current hybrid torus-normaliser model")
println("does not contain the required non-normalising PSL2(13) Bruhat t.")
println("")
println("Next mathematical move:")
println("leave the hybrid torus-normaliser model and move toward")
println("a genuine F4(7) / centraliser / extended-centraliser construction.")
println("============================================================")
println("END STEP 24")
println("============================================================")

############################################################
# STEP 25:
# IDENTIFY THE NORMALISING t0 AS AN INTERNAL ELEMENT OF B=<g,f>
############################################################

println("============================================================")
println("STEP 25: IDENTIFY THE NORMALISING t0 INSIDE B")
println("============================================================")

# Rebuild f0, t0, B0 cleanly.

f0 = Elem(Zero4(), Zero4(), wf)

w139 = involution_ws[139]
t0 = Elem(Zero4(), Zero4(), w139)

B0 = Any[]
B0Expr = String[]
seenB0 = Set{String}()

for i in 0:12
    for j in 0:5
        b = HMul(HPow(g,i), HPow(f0,j))
        k = ElemKey(b)

        if !(k in seenB0)
            push!(seenB0, k)
            push!(B0, b)
            push!(B0Expr, "g^$(i)*f^$(j)")
        end
    end
end

println("Size of B0 = ", length(B0))

println("------------------------------------------------------------")
println("Powers of f0 compared with t0")

for j in 0:5
    fj = HPow(f0,j)

    println("j = ", j,
            " | Order(f0^j) = ", HOrder(fj),
            " | Trace(f0^j) = ", TraceElemInt(fj),
            " | f0^j equals t0? ", HEqual(fj,t0))
end

println("------------------------------------------------------------")
println("Direct check:")
println("Order(t0) = ", HOrder(t0))
println("Trace(t0) = ", TraceElemInt(t0))
println("t0 equals f0^3? ", HEqual(t0, HPow(f0,3)))

println("------------------------------------------------------------")
println("Finding expression of t0 inside B0")

found_expr = false

for idx in eachindex(B0)
    if HEqual(B0[idx], t0)
        println("t0 is inside B0 as: ", B0Expr[idx])
        global found_expr = true
    end
end

if !found_expr
    println("t0 was not found inside B0. This would be unexpected.")
end

println("------------------------------------------------------------")
println("Counting b*t0 order-3 relations by b = g^i*f^j")

count_by_j = Dict{Int,Int}()

examples = Any[]

for i in 0:12
    for j in 0:5
        b = HMul(HPow(g,i), HPow(f0,j))
        x = HMul(b, t0)

        if IsOrder3Element(x)
            count_by_j[j] = get(count_by_j, j, 0) + 1

            if length(examples) < 30
                push!(examples, (
                    i = i,
                    j = j,
                    order_bt = HOrder(x)
                ))
            end
        end
    end
end

println("Counts by f-exponent j:")
for j in sort(collect(keys(count_by_j)))
    println("  j = ", j, " gives ", count_by_j[j], " order-3 relations")
end

println("First examples:")
for ex in examples
    println("  b = g^", ex.i, "*f^", ex.j,
            " | Order(b*t0) = ", ex.order_bt)
end

println("------------------------------------------------------------")
println("Computing <g,f0,t0>")

size_gft0, completed_gft0 = GeneratedSubgroupSizeFast(
    [g, f0, t0];
    MAX_SIZE = 50000
)

println("|<g,f0,t0>| = ", size_gft0)
println("Subgroup closure completed? ", completed_gft0)

if size_gft0 == length(B0)
    println("<g,f0,t0> equals B0.")
else
    println("<g,f0,t0> is not equal to B0. Check this carefully.")
end

println("============================================================")
println("STEP 25 FINAL CONCLUSION")
println("============================================================")

if HEqual(t0, HPow(f0,3)) && size_gft0 == length(B0)
    println("The only Weyl-level Bruhat-compatible t is just f0^3.")
    println("It is already inside B0=<g,f0>.")
    println("The order-3 relations b*t0 are internal relations inside B0.")
    println("Therefore this t is not the PSL2(13) Bruhat generator.")
    println("")
    println("Conclusion:")
    println("The hybrid torus-normaliser model is exhausted.")
    println("The next stage should move to a genuine F4(7) or")
    println("centraliser / extended-centraliser model, following Walton's method.")
else
    println("The result is not the expected clean internal t=f0^3 case.")
    println("Inspect the outputs above carefully.")
end

println("============================================================")
println("END STEP 25")
println("============================================================")

############################################################
# STEP 26:
# WRITE AND OPTIONALLY RUN THE ABSTRACT PSL2(13) GAP SCRIPT
############################################################

println("============================================================")
println("STEP 26: WRITE GAP SCRIPT FOR ABSTRACT PSL2(13) FINGERPRINT")
println("============================================================")

GAP_STEP_26_SCRIPT = raw"""
############################################################
# STEP 26:
# Abstract PSL2(13) Bruhat fingerprint
#
# Purpose:
#   Our hybrid model only found the internal involution f^3.
#   Now we return to abstract PSL2(13) and record what the
#   genuine external Bruhat involution t should look like.
#
# We want:
#   g order 13
#   f order 6
#   <g,f> = 13:6
#   f acts on <g> by exponent 10
#   t order 2
#   t does NOT normalise <g>
#   there exists b in <g,f> with Order(b*t)=3
#   <g,f,t> = PSL2(13), order 1092
#
# This gives the correct target fingerprint for the next
# genuine F4(7) / centraliser search.
############################################################

Print("\n============================================================\n");
Print("STEP 26: ABSTRACT PSL2(13) BRUHAT FINGERPRINT\n");
Print("============================================================\n");

############################################################
# Construct PSL2(13)
############################################################

H := PSL(2,13);;
Print("Order(H) = ", Size(H), "\n");

elts := Elements(H);;

############################################################
# Choose g of order 13
############################################################

g_candidates := Filtered(elts, x -> Order(x) = 13);;
Print("Number of elements of order 13 = ", Length(g_candidates), "\n");

g := g_candidates[1];;
P := Group(g);;

Print("Order(g) = ", Order(g), "\n");
Print("Order(<g>) = ", Size(P), "\n");

NH_P := Normalizer(H,P);;
Print("Order(N_H(<g>)) = ", Size(NH_P), "\n");
Print("StructureDescription(N_H(<g>)) = ", StructureDescription(NH_P), "\n");

############################################################
# Helper: action exponent on <g>
############################################################

ActionExponentOnG := function(x,g)
    local y,k;

    y := g^x;

    for k in [1..12] do
        if y = g^k then
            return k;
        fi;
    od;

    return fail;
end;;

############################################################
# Find f of order 6 in N_H(<g>) acting by exponent 10
############################################################

f_candidates := [];;

for x in Elements(NH_P) do
    if Order(x) = 6 then
        if ActionExponentOnG(x,g) = 10 then
            Add(f_candidates,x);
        fi;
    fi;
od;

Print("Number of order-6 f candidates with action exponent 10 = ",
      Length(f_candidates), "\n");

if Length(f_candidates) = 0 then
    Error("No f found with action exponent 10.");
fi;

f := f_candidates[1];;
B := Group(g,f);;

Print("Order(f) = ", Order(f), "\n");
Print("Action exponent of f on <g> = ", ActionExponentOnG(f,g), "\n");
Print("Order(<g,f>) = ", Size(B), "\n");
Print("StructureDescription(<g,f>) = ", StructureDescription(B), "\n");

############################################################
# Confirm internal involution f^3
############################################################

t_internal := f^3;;

Print("\n------------------------------------------------------------\n");
Print("Internal involution check\n");
Print("Order(f^3) = ", Order(t_internal), "\n");
Print("Does f^3 normalise <g>? ", t_internal in Normalizer(H,P), "\n");
Print("Action exponent of f^3 on <g> = ",
      ActionExponentOnG(t_internal,g), "\n");
Print("Order(<g,f,f^3>) = ", Size(Group(g,f,t_internal)), "\n");

internal_order3_count := 0;;

for b in Elements(B) do
    if Order(b*t_internal) = 3 then
        internal_order3_count := internal_order3_count + 1;
    fi;
od;

Print("Number of b in B with Order(b*f^3)=3 = ",
      internal_order3_count, "\n");

############################################################
# Search for genuine external Bruhat involutions t
############################################################

Print("\n------------------------------------------------------------\n");
Print("Searching for genuine external Bruhat involutions\n");

all_involutions := Filtered(elts, x -> Order(x) = 2);;
Print("Number of involutions in H = ", Length(all_involutions), "\n");

GoodTs := [];;

for t in all_involutions do

    # The genuine Bruhat t should not lie in B.
    if t in B then
        continue;
    fi;

    # It should not normalise <g>.
    if t in Normalizer(H,P) then
        continue;
    fi;

    # It should close <g,f> to H.
    if Size(Group(g,f,t)) <> Size(H) then
        continue;
    fi;

    # It should satisfy the order-3 Bruhat relation for some b in B.
    for b in Elements(B) do
        if Order(b*t) = 3 then
            Add(GoodTs, [t,b]);
            break;
        fi;
    od;
od;

Print("Number of genuine external Bruhat t pairs found = ",
      Length(GoodTs), "\n");

if Length(GoodTs) = 0 then
    Error("No genuine external Bruhat t found. Something is wrong.");
fi;

t := GoodTs[1][1];;
b := GoodTs[1][2];;

Print("\n============================================================\n");
Print("FIRST GENUINE BRUHAT t\n");
Print("============================================================\n");

Print("Order(t) = ", Order(t), "\n");
Print("t in B? ", t in B, "\n");
Print("t normalises <g>? ", t in Normalizer(H,P), "\n");
Print("Order(b*t) = ", Order(b*t), "\n");
Print("Order(<g,f,t>) = ", Size(Group(g,f,t)), "\n");
Print("StructureDescription(<g,f,t>) = ",
      StructureDescription(Group(g,f,t)), "\n");

############################################################
# Express the Bruhat witness b as g^i f^j
############################################################

Print("\n------------------------------------------------------------\n");
Print("Expression of b in B=<g,f>\n");

found_b_expr := false;;

for i in [0..12] do
    for j in [0..5] do
        if b = g^i * f^j then
            Print("b = g^", i, " * f^", j, "\n");
            found_b_expr := true;
        fi;
    od;
od;

if not found_b_expr then
    Print("Could not express b as g^i*f^j. Check multiplication convention.\n");
fi;

############################################################
# Compare internal and external involutions
############################################################

Print("\n============================================================\n");
Print("INTERNAL VS EXTERNAL INVOLUTION COMPARISON\n");
Print("============================================================\n");

Print("Internal t0 = f^3:\n");
Print("  Order = ", Order(t_internal), "\n");
Print("  t0 in B? ", t_internal in B, "\n");
Print("  t0 normalises <g>? ", t_internal in Normalizer(H,P), "\n");
Print("  Order(<g,f,t0>) = ", Size(Group(g,f,t_internal)), "\n");

Print("External Bruhat t:\n");
Print("  Order = ", Order(t), "\n");
Print("  t in B? ", t in B, "\n");
Print("  t normalises <g>? ", t in Normalizer(H,P), "\n");
Print("  Order(<g,f,t>) = ", Size(Group(g,f,t)), "\n");

############################################################
# Optional: count all good external t, not just pairs
############################################################

GoodTSet := Set(List(GoodTs, pair -> pair[1]));;

Print("\nNumber of distinct genuine external Bruhat t elements = ",
      Length(GoodTSet), "\n");

Print("============================================================\n");
Print("STEP 26 FINAL CONCLUSION\n");
Print("============================================================\n");

Print("The abstract PSL2(13) model confirms the distinction:\n");
Print("  f^3 is an internal involution in the 13:6 normaliser.\n");
Print("  The real Bruhat t is an external involution.\n");
Print("  It does not normalise <g>.\n");
Print("  It closes <g,f> to PSL2(13).\n");
Print("\n");
Print("Therefore the missing F4(7) t must be external to the\n");
Print("torus-normaliser model used so far.\n");

Print("============================================================\n");
Print("END STEP 26\n");
Print("============================================================\n");
"""

gap_filename = "Step26_Abstract_PSL2_13_Bruhat_Fingerprint.g"
write(gap_filename, GAP_STEP_26_SCRIPT)

println("Wrote GAP Step 26 script to: ", gap_filename)

if Sys.which("gap") !== nothing
    println("GAP command found. Running Step 26 GAP script now:")
    println("------------------------------------------------------------")
    run(`gap -q $gap_filename`)
else
    println("GAP command was not found in PATH.")
    println("Step 26 has still been written to:")
    println("  ", gap_filename)
    println("Run it manually later with:")
    println("  gap -q ", gap_filename)
end

println("============================================================")
println("END COMBINED SCRIPT")
println("============================================================")

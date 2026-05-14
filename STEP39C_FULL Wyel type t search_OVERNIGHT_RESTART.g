############################################################
# STEP 39C FULL FRESH OVERNIGHT RESTART
#
# Paste at gap> after:
#
#   using Oscar
#   GAP.prompt()
#
# This rebuilds everything from zero:
#   - adjoint F4 over GF(7)
#   - Chevalley basis
#   - root group matrices
#   - Weyl lifts
#   - frozen f of order 6 with trace profile 2,-2,-4
#   - extension field GF(7^12)
#   - all 12 signed Kac lines for g
#   - 36 trace -4 exact-inverting Weyl-lift t candidates
#   - FULL Bruhat/order-3 test over all 78 elements b=g^i f^j
#
# This is the overnight version.
############################################################

LogTo("STEP39C_FULL_OVERNIGHT_LOG.txt");

Print("\n============================================================\n");
Print("STEP 39C FULL FRESH OVERNIGHT RESTART\n");
Print("============================================================\n");

startTime39 := Runtime();;

############################################################
# PART 0. Basic setup
############################################################

LoadPackage("sla");

F7_39 := GF(7);;
Fext39 := GF(7,12);;

one7_39 := One(F7_39);;
zero7_39 := Zero(F7_39);;

oneExt39 := One(Fext39);;
zeroExt39 := Zero(Fext39);;

trace_f_target_39  := 2 * one7_39;;
trace_f2_target_39 := 5 * one7_39;;   # -2 mod 7
trace_t_target_39  := 3 * one7_39;;   # -4 mod 7

Print("Fields ready.\n");
Print("GF(7) trace targets: f=", trace_f_target_39,
      ", f^2=", trace_f2_target_39,
      ", t/f^3=", trace_t_target_39, "\n");

############################################################
# PART 1. Helper functions
############################################################

TraceMat39 := function(M)
    local s, i;

    s := M[1][1] * 0;

    for i in [1..Length(M)] do
        s := s + M[i][i];
    od;

    return s;
end;;

TraceExt39 := function(M)
    local s, i;

    s := M[1][1] * 0;

    for i in [1..Length(M)] do
        s := s + M[i][i];
    od;

    return s;
end;;

ModInt39 := function(n, m)
    local r;

    r := n mod m;

    if r < 0 then
        r := r + m;
    fi;

    return r;
end;;

FFEToSignedInt7_39 := function(a)
    local n;

    if a = Zero(F7_39) then
        return 0;
    fi;

    n := IntFFE(a);

    if n > 3 then
        n := n - 7;
    fi;

    return n;
end;;

LiftMatrixToExt39 := function(M)
    local N, i, j, row;

    N := [];

    for i in [1..Length(M)] do
        row := [];
        for j in [1..Length(M[i])] do
            Add(row, M[i][j] * oneExt39);
        od;
        Add(N, row);
    od;

    return N;
end;;

MatInList39 := function(M, L)
    local X;

    for X in L do
        if M = X then
            return true;
        fi;
    od;

    return false;
end;;

UniqueMatrixCount39 := function(L)
    local U, X;

    U := [];

    for X in L do
        if not MatInList39(X, U) then
            Add(U, X);
        fi;
    od;

    return Length(U);
end;;

BuildNormalForms39 := function(g, f)
    local B, i, j;

    B := [];

    for i in [0..12] do
        for j in [0..5] do
            Add(B, rec(i := i, j := j, elt := g^i * f^j));
        od;
    od;

    return B;
end;;

ActionExponentOnG39 := function(g, x)
    local gx, k;

    gx := g^x;

    for k in [0..12] do
        if gx = g^k then
            return k;
        fi;
    od;

    return fail;
end;;

GoodTraceProfileF39 := function(x)
    if Order(x) <> 6 then
        return false;
    fi;

    if TraceMat39(x) <> trace_f_target_39 then
        return false;
    fi;

    if TraceMat39(x^2) <> trace_f2_target_39 then
        return false;
    fi;

    if TraceMat39(x^3) <> trace_t_target_39 then
        return false;
    fi;

    return true;
end;;

############################################################
# PART 2. Build adjoint F4 over GF(7)
############################################################

Print("\n============================================================\n");
Print("PART 2. BUILDING ADJOINT F4 OVER GF(7)\n");
Print("============================================================\n");

L39 := SimpleLieAlgebra("F", 4, F7_39);;

CB39 := ChevalleyBasis(L39);;

pos39 := CB39[1];;
neg39 := CB39[2];;
cart39 := CB39[3];;

basisVecs39 := Concatenation(pos39, neg39, cart39);;
BAS39 := Basis(L39, basisVecs39);;

Print("Dimension L39 = ", Dimension(L39), "\n");
Print("Positive root vectors = ", Length(pos39), "\n");
Print("Negative root vectors = ", Length(neg39), "\n");
Print("Cartan vectors = ", Length(cart39), "\n");
Print("Total basis length = ", Length(basisVecs39), "\n");

AdjMat39 := function(x)
    return AdjointMatrix(BAS39, x);
end;;

############################################################
# PART 3. Root group matrices and Weyl lifts
############################################################

Print("\n============================================================\n");
Print("PART 3. BUILDING ROOT GROUP MATRICES AND WEYL LIFTS\n");
Print("============================================================\n");

RootGroupMatrix39 := function(A, t)
    local n, M, Apow, fact, k, coeff;

    n := Length(A);

    M := IdentityMat(n, F7_39);
    Apow := IdentityMat(n, F7_39);
    fact := One(F7_39);

    for k in [1..6] do
        Apow := Apow * A;
        fact := fact * (k * One(F7_39));
        coeff := (t^k) / fact;
        M := M + coeff * Apow;
    od;

    return M;
end;;

rootMats39 := [];;
rootVecs39 := Concatenation(pos39, neg39);;

for i in [1..Length(rootVecs39)] do
    Add(rootMats39, RootGroupMatrix39(AdjMat39(rootVecs39[i]), one7_39));
od;

Print("Built root group matrices = ", Length(rootMats39), "\n");

WeylLifts39 := [];;

for i in [1..24] do
    Add(WeylLifts39,
        RootGroupMatrix39(AdjMat39(pos39[i]), one7_39)
        * RootGroupMatrix39(AdjMat39(neg39[i]), -one7_39)
        * RootGroupMatrix39(AdjMat39(pos39[i]), one7_39)
    );
od;

Print("Built Weyl lift generators = ", Length(WeylLifts39), "\n");

Wlift39 := Group(WeylLifts39);;

Print("Size(Wlift39) = ", Size(Wlift39), "\n");

############################################################
# PART 4. Build frozen f
############################################################

Print("\n============================================================\n");
Print("PART 4. BUILDING FROZEN f\n");
Print("============================================================\n");

fWord39 := [5,24,2,14,8,17,9,6,7,16,5,23,19,9,3,6,6,15,9,1];;

BuildFromWord39 := function(word)
    local x, i;

    x := IdentityMat(52, F7_39);

    for i in word do
        x := x * WeylLifts39[i];
    od;

    return x;
end;;

f39 := BuildFromWord39(fWord39);;

Print("Order(f39) = ", Order(f39), "\n");
Print("Trace(f39) = ", TraceMat39(f39), "\n");
Print("Trace(f39^2) = ", TraceMat39(f39^2), "\n");
Print("Trace(f39^3) = ", TraceMat39(f39^3), "\n");
Print("GoodTraceProfileF39(f39) = ", GoodTraceProfileF39(f39), "\n");

if not GoodTraceProfileF39(f39) then
    Error("Frozen f did not have the expected trace profile. Stop here.");
fi;

fExt39 := LiftMatrixToExt39(f39);;

############################################################
# PART 5. Compute Cartan labels from the actual Chevalley basis
############################################################

Print("\n============================================================\n");
Print("PART 5. COMPUTING CARTAN LABELS FROM ACTUAL BASIS\n");
Print("============================================================\n");

RootLabels39 := [];;
rootVecs39 := Concatenation(pos39, neg39);;

for i in [1..48] do
    localLabels39 := [];

    for j in [1..4] do
        br39 := cart39[j] * rootVecs39[i];
        coeffs39 := Coefficients(BAS39, br39);
        Add(localLabels39, FFEToSignedInt7_39(coeffs39[i]));
    od;

    Add(RootLabels39, localLabels39);
od;

Print("Computed RootLabels39 length = ", Length(RootLabels39), "\n");
Print("First few root labels:\n");

for i in [1..6] do
    Print("  root label ", i, " = ", RootLabels39[i], "\n");
od;

############################################################
# PART 6. Build order-13 torus element from Kac line
############################################################

Print("\n============================================================\n");
Print("PART 6. SETTING UP KAC-LINE CONSTRUCTION\n");
Print("============================================================\n");

primitive13_39 := Z(7,12)^QuoInt(7^12 - 1, 13);;

Print("Order(primitive13_39) = ", Order(primitive13_39), "\n");

BuildGFromKacLine39 := function(kac)
    local diag, i, j, dot, exp, val;

    diag := [];

    for i in [1..48] do
        dot := 0;

        for j in [1..4] do
            dot := dot + RootLabels39[i][j] * kac[j];
        od;

        exp := ModInt39(dot, 13);
        val := primitive13_39^exp;

        Add(diag, val);
    od;

    for i in [1..4] do
        Add(diag, oneExt39);
    od;

    return DiagonalMat(diag);
end;;

############################################################
# PART 7. Build 36 exact-inverting trace -4 t-candidates
############################################################

Print("\n============================================================\n");
Print("PART 7. FINDING TRACE -4 EXACT-INVERTING t-CANDIDATES\n");
Print("============================================================\n");

wElems39 := Elements(Wlift39);;

Print("Number of Weyl-lift elements = ", Length(wElems39), "\n");

invols39 := [];;

for x39 in wElems39 do
    if x39^2 = IdentityMat(52, F7_39) and x39 <> IdentityMat(52, F7_39) then
        Add(invols39, x39);
    fi;
od;

Print("Number of Weyl-lift involutions = ", Length(invols39), "\n");

exactInverters39 := [];;

for t39 in invols39 do
    if f39^t39 = f39^-1 then
        Add(exactInverters39, t39);
    fi;
od;

Print("Number of exact-inverting Weyl-lift involutions = ",
      Length(exactInverters39), "\n");

GoodTCandidates39 := [];;

for t39 in exactInverters39 do
    if TraceMat39(t39) = trace_t_target_39 then
        Add(GoodTCandidates39, t39);
    fi;
od;

Print("Number of trace -4 exact-inverting t-candidates = ",
      Length(GoodTCandidates39), "\n");

if Length(GoodTCandidates39) <> 36 then
    Print("WARNING: Expected 36 candidates, but got ",
          Length(GoodTCandidates39), ". Continuing anyway.\n");
fi;

############################################################
# PART 8. Define all 12 signed Kac lines
############################################################

Print("\n============================================================\n");
Print("PART 8. DEFINING 12 SIGNED KAC LINES\n");
Print("============================================================\n");

BaseKacLines39 := [
    [1,3,8,12],
    [1,6,12,3],
    [1,7,9,0],
    [1,9,3,7],
    [1,10,0,4],
    [1,11,10,1]
];;

SignedKacLines39 := [];;

for line39 in BaseKacLines39 do
    Add(SignedKacLines39,
        rec(sign := 1,
            kac := List(line39, x -> ModInt39(x, 13)))
    );

    Add(SignedKacLines39,
        rec(sign := -1,
            kac := List(line39, x -> ModInt39(-x, 13)))
    );
od;

Print("Number of signed Kac lines = ", Length(SignedKacLines39), "\n");

for i in [1..Length(SignedKacLines39)] do
    Print("  line #", i,
          ", sign=", SignedKacLines39[i].sign,
          ", kac=", SignedKacLines39[i].kac, "\n");
od;

############################################################
# PART 9. FULL OVERNIGHT BRUHAT TEST
############################################################

Print("\n============================================================\n");
Print("PART 9. FULL OVERNIGHT BRUHAT TEST\n");
Print("============================================================\n");

STOP_AFTER_FIRST_HIT39 := false;;
TRY_GROUP_SIZE_ON_HIT39 := false;;

totalHits39 := 0;;
totalBTests39 := 0;;
AllHits39 := [];;

IdExt39 := IdentityMat(52, Fext39);;

for lineIndex39 in [1..Length(SignedKacLines39)] do

    kacRec39 := SignedKacLines39[lineIndex39];;
    kac39 := kacRec39.kac;;

    Print("\n------------------------------------------------------------\n");
    Print("FULL TEST: line #", lineIndex39,
          ", sign=", kacRec39.sign,
          ", kac=", kac39, "\n");

    gExt39 := BuildGFromKacLine39(kac39);;

    Print("g^13 = 1? ", gExt39^13 = IdExt39, "\n");
    Print("g is nontrivial? ", gExt39 <> IdExt39, "\n");
    Print("Order(g) = ", Order(gExt39), "\n");
    Print("Trace(g)=0? ", TraceExt39(gExt39) = zeroExt39, "\n");
    Print("Trace(g) = ", TraceExt39(gExt39), "\n");

    actExpF39 := ActionExponentOnG39(gExt39, fExt39);;
    Print("Action exponent of f on <g> = ", actExpF39, "\n");
    Print("Check g^f = g^10 ? ", gExt39^fExt39 = gExt39^10, "\n");

    BForms39 := BuildNormalForms39(gExt39, fExt39);;
    BElts39 := List(BForms39, r -> r.elt);;
    distinctB39 := UniqueMatrixCount39(BElts39);;

    Print("Distinct normal forms g^i f^j = ", distinctB39, "\n");

    if not (gExt39^13 = IdExt39 and gExt39 <> IdExt39
            and TraceExt39(gExt39) = zeroExt39
            and actExpF39 = 10
            and distinctB39 = 78) then

        Print("WARNING: This Kac line failed local 13:6 checks. Skipping line.\n");

    else

        lineHits39 := 0;;

        for tIndex39 in [1..Length(GoodTCandidates39)] do

            t39 := GoodTCandidates39[tIndex39];;
            tExt39 := LiftMatrixToExt39(t39);;

            basicOK39 := true;;

            if not (tExt39^2 = IdExt39 and tExt39 <> IdExt39) then
                basicOK39 := false;
            fi;

            if not (fExt39^tExt39 = fExt39^-1) then
                basicOK39 := false;
            fi;

            if MatInList39(tExt39, BElts39) then
                basicOK39 := false;
            fi;

            if ActionExponentOnG39(gExt39, tExt39) <> fail then
                basicOK39 := false;
            fi;

            if basicOK39 then

                for bRec39 in BForms39 do

                    totalBTests39 := totalBTests39 + 1;;

                    bt39 := bRec39.elt * tExt39;;

                    if bt39 <> IdExt39 and bt39^3 = IdExt39 then

                        totalHits39 := totalHits39 + 1;;
                        lineHits39 := lineHits39 + 1;;

                        hitRec39 := rec(
                            lineIndex := lineIndex39,
                            sign := kacRec39.sign,
                            kac := kac39,
                            tIndex := tIndex39,
                            i := bRec39.i,
                            j := bRec39.j
                        );;

                        Add(AllHits39, hitRec39);

                        Print("\n******************** HIT FOUND ********************\n");
                        Print("line #", lineIndex39,
                              ", sign=", kacRec39.sign,
                              ", kac=", kac39, "\n");
                        Print("t candidate index = ", tIndex39, "\n");
                        Print("Bruhat witness b = g^", bRec39.i,
                              " * f^", bRec39.j, "\n");
                        Print("Check (b*t)^3 = 1 and b*t <> 1: true\n");

                        if TRY_GROUP_SIZE_ON_HIT39 then
                            Hhit39 := Group([gExt39, fExt39, tExt39]);;
                            Print("Attempting Size(<g,f,t>)...\n");
                            Print("Size(<g,f,t>) = ", Size(Hhit39), "\n");
                        fi;

                        Print("***************************************************\n");

                        if STOP_AFTER_FIRST_HIT39 then
                            Print("STOP_AFTER_FIRST_HIT39 is true. Stopping.\n");
                            Print("Total hits = ", totalHits39, "\n");
                            Print("Total b-tests = ", totalBTests39, "\n");
                            Print("Elapsed ms = ", Runtime() - startTime39, "\n");
                            Error("Stopped after first hit by user setting.");
                        fi;

                    fi;

                od;

            else
                Print("  t index ", tIndex39,
                      " failed basic external filter for this line.\n");
            fi;

            if tIndex39 mod 6 = 0 then
                Print("  full-tested t up to index ", tIndex39,
                      " for line #", lineIndex39,
                      " | line hits = ", lineHits39,
                      " | total hits = ", totalHits39,
                      " | total b-tests = ", totalBTests39,
                      " | elapsed ms = ", Runtime() - startTime39, "\n");
            fi;

        od;

        Print("Finished line #", lineIndex39,
              " | line hits = ", lineHits39,
              " | total hits = ", totalHits39,
              " | total b-tests = ", totalBTests39,
              " | elapsed ms = ", Runtime() - startTime39, "\n");

    fi;

od;

############################################################
# PART 10. Final report
############################################################

Print("\n============================================================\n");
Print("STEP 39C FULL OVERNIGHT FINAL REPORT\n");
Print("============================================================\n");

Print("Number of signed Kac lines tested = ", Length(SignedKacLines39), "\n");
Print("Number of trace -4 exact-inverting t-candidates = ",
      Length(GoodTCandidates39), "\n");
Print("Total b-tests = ", totalBTests39, "\n");
Print("Total Bruhat/order-3 hits = ", totalHits39, "\n");
Print("Elapsed ms = ", Runtime() - startTime39, "\n");

if totalHits39 = 0 then
    Print("\nCONCLUSION:\n");
    Print("No Bruhat/order-3 hit was found among the 36 pure Weyl-lift exact-inverting t-candidates,\n");
    Print("over all 12 signed Kac lines and all 78 elements b=g^i f^j in B.\n");
    Print("This strongly suggests that pure Weyl-lift t-candidates are not enough,\n");
    Print("and the next search should include root-group/unipotent/extended-centraliser data.\n");
else
    Print("\nHITS:\n");

    for h39 in AllHits39 do
        Print("line #", h39.lineIndex,
              ", sign=", h39.sign,
              ", kac=", h39.kac,
              ", t index=", h39.tIndex,
              ", witness b=g^", h39.i, "*f^", h39.j, "\n");
    od;
fi;

Print("\nLog file: STEP39C_FULL_OVERNIGHT_LOG.txt\n");
Print("Finished STEP 39C FULL OVERNIGHT RESTART.\n");

LogTo();

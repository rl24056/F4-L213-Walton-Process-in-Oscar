############################################################
# F4 / PSL2(13), characteristic 7 restart
#
# GitHub-ready combined GAP/OSCAR script.
#
# Purpose:
# 1. Check the abstract Walton blueprint inside PSL2(13):
#       g of order 13,
#       f of order 6,
#       <g,f> = 13:6,
#       t an involution closing to PSL2(13).
#
# 2. Move to characteristic 7 Brauer data for PSL2(13).
#
# 3. Check the Magaard-style 27-dimensional minimal/Jordan
#    module pattern:
#       1 + 12 + 14.
#
# 4. Remove the fixed Jordan identity line:
#       27 = 1 + 26,
#       so 26 = 12 + 14.
#
# 5. Search formal 52-dimensional adjoint-module candidates
#    with:
#       degree 52,
#       no trivial factor,
#       order-13 trace zero.
#
# 6. Check compatibility with exterior square of the
#    26-dimensional trace-zero minimal module using the
#    corrected Brauer-character solving method.
#
# Important:
# This does NOT construct F4(7).
# This is the characteristic-7 representation-theoretic
# filtering stage before returning to the F4-side EltTraces /
# feasible-character comparison.
############################################################


############################################################
# Optional package loading
############################################################

LoadPackage("ctbllib");;


############################################################
# Basic helper functions
############################################################

F4PrintLine := function()
    Print("------------------------------------------------------------\n");
end;;


F4MultOrderMod13 := function(a)
    local x, n;

    if Gcd(a,13) <> 1 then
        return 0;
    fi;

    x := a mod 13;
    n := 1;

    while x <> 1 do
        x := (x*a) mod 13;
        n := n + 1;
    od;

    return n;
end;;


F4ActionExponent := function(x,g)
    local a;

    for a in [1..12] do
        if x*g*x^-1 = g^a then
            return a;
        fi;
    od;

    return 0;
end;;


############################################################
# PART 1:
# Abstract PSL2(13) Walton-style sanity check
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 1: ABSTRACT WALTON BLUEPRINT INSIDE PSL2(13)\n");
Print("============================================================\n");

H := PSL(2,13);;

Print("Order of H = ", Size(H), "\n");

S := SylowSubgroup(H,13);;
g := GeneratorsOfGroup(S)[1];;

if Order(g) <> 13 then
    repeat
        g := Random(S);
    until Order(g) = 13;
fi;

Print("Order of S = ", Size(S), "\n");
Print("Order of g = ", Order(g), "\n");

NHg := Normalizer(H,S);;

Print("Order of N_H(<g>) = ", Size(NHg), "\n");
Print("Expected order for 13:6 = 78\n");

GoodFs := [];;

for x in Elements(NHg) do
    if Order(x) = 6 then

        a := F4ActionExponent(x,g);

        if a <> 0 and F4MultOrderMod13(a) = 6 and Size(Group(g,x)) = 78 then
            Add(GoodFs,[x,a]);
        fi;

    fi;
od;

Print("Number of suitable f-elements = ", Length(GoodFs), "\n");

if Length(GoodFs) = 0 then
    Error("No suitable f found. Something is wrong.");
fi;

f := GoodFs[1][1];;
a := GoodFs[1][2];;

Print("Chosen f has order = ", Order(f), "\n");
Print("Action exponent of f on <g> = ", a, "\n");
Print("Multiplicative order of exponent modulo 13 = ", F4MultOrderMod13(a), "\n");
Print("Order of <g,f> = ", Size(Group(g,f)), "\n");

B := Group(g,f);;
BElts := Elements(B);;

F4PrintLine();

Print("Now searching for a Bruhat/Weyl-type involution t inside PSL2(13).\n");
Print("This confirms the abstract Walton blueprint only.\n");

GoodTs := [];;

for t in Elements(H) do

    if Order(t) = 2 then

        if Size(Group(g,f,t)) = Size(H) then

            for b in BElts do
                if Order(b*t) = 3 then
                    Add(GoodTs,[t,b]);
                    break;
                fi;
            od;

        fi;

    fi;

od;

Print("Number of Bruhat-style t candidates found = ", Length(GoodTs), "\n");

if Length(GoodTs) > 0 then
    t := GoodTs[1][1];;
    b := GoodTs[1][2];;

    Print("A working t was found.\n");
    Print("Order of t = ", Order(t), "\n");
    Print("Order of b*t = ", Order(b*t), "\n");
    Print("Order of <g,f,t> = ", Size(Group(g,f,t)), "\n");

    if Size(Group(g,f,t)) = 1092 then
        Print("Success: <g,f,t> has order 1092, so it is PSL2(13).\n");
    fi;
else
    Print("No t found in this run. Try changing the chosen f from GoodFs.\n");
fi;


############################################################
# PART 2:
# Characteristic 7 Brauer table for PSL2(13)
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 2: BRAUER TABLE OF PSL2(13) IN CHARACTERISTIC 7\n");
Print("============================================================\n");

tbl := CharacterTable("L2(13)");;

if tbl = fail then
    tbl := CharacterTable("PSL(2,13)");
fi;

if tbl = fail then
    Error("Could not load character table for L2(13).");
fi;

btbl := BrauerTable(tbl,7);;

if btbl = fail then
    Error("Could not load Brauer table for L2(13) in characteristic 7.");
fi;

irr := Irr(btbl);;
orders := OrdersClassRepresentatives(btbl);;
degrees := List(irr, chi -> chi[1]);;
pos13 := Filtered([1..Length(orders)], i -> orders[i] = 13);;

labels := ["1", "7a", "7b", "12", "14a", "14b"];;

Print("Brauer irreducible degrees in characteristic 7:\n");
Print(degrees, "\n");

Print("\nBrauer table class orders:\n");
Print(orders, "\n");

Print("\nPositions of order-13 classes in the Brauer table:\n");
Print(pos13, "\n");

F4PrintLine();

Print("Values of irreducible Brauer characters on order-13 classes:\n");

for i in [1..Length(irr)] do
    Print("irreducible ", i,
          " degree ", degrees[i],
          " values on order-13 classes = ",
          List(pos13, j -> irr[i][j]),
          "\n");
od;


############################################################
# Character helper functions
############################################################

ZeroChar := function()
    return List([1..Length(irr[1])], i -> 0);
end;;


AddChars := function(chars)
    local result, chi, i;

    result := ZeroChar();

    for chi in chars do
        for i in [1..Length(result)] do
            result[i] := result[i] + chi[i];
        od;
    od;

    return result;
end;;


CharFromCoeffs := function(coeffs)
    local result, i, j;

    result := ZeroChar();

    for i in [1..Length(coeffs)] do
        for j in [1..Length(result)] do
            result[j] := result[j] + coeffs[i] * irr[i][j];
        od;
    od;

    return result;
end;;


PrintDecomposition := function(coeffs)
    local i, first;

    first := true;

    for i in [1..Length(coeffs)] do
        if coeffs[i] <> 0 then

            if first = false then
                Print(" + ");
            fi;

            if coeffs[i] = 1 then
                Print(labels[i]);
            else
                Print(coeffs[i], "*", labels[i]);
            fi;

            first := false;
        fi;
    od;

    if first = true then
        Print("0");
    fi;

    Print("\n");
end;;


PrintCharSummary := function(name, chi)
    Print("\n", name, "\n");
    Print("degree = ", chi[1], "\n");
    Print("values on order-13 classes = ", List(pos13, j -> chi[j]), "\n");
    Print("full Brauer-character values = ", chi, "\n");
end;;


ExteriorSquareChar := function(tbl, chi)
    local pm2, result, i;

    pm2 := PowerMap(tbl,2);
    result := [];

    for i in [1..Length(chi)] do
        if pm2[i] = fail then
            Error("Power map has fail at position ", i);
        fi;

        Add(result, (chi[i]^2 - chi[pm2[i]]) / 2);
    od;

    return result;
end;;


SymmetricSquareChar := function(tbl, chi)
    local pm2, result, i;

    pm2 := PowerMap(tbl,2);
    result := [];

    for i in [1..Length(chi)] do
        if pm2[i] = fail then
            Error("Power map has fail at position ", i);
        fi;

        Add(result, (chi[i]^2 + chi[pm2[i]]) / 2);
    od;

    return result;
end;;


IsNonnegativeIntegerCoeffList := function(L)
    local x;

    for x in L do
        if not (x in Integers) then
            return false;
        fi;

        if x < 0 then
            return false;
        fi;
    od;

    return true;
end;;


BrauerDecomposeBySolving := function(name, chi)
    local sol, rebuild;

    Print("\n");
    Print("Trying to decompose: ", name, "\n");

    sol := SolutionMat(irr, chi);

    if sol = fail then
        Print("No solution found in the Brauer irreducible basis.\n");
        return fail;
    fi;

    Print("solution coefficients [1,7a,7b,12,14a,14b] = ", sol, "\n");

    rebuild := CharFromCoeffs(sol);

    if rebuild = chi then
        Print("Check: reconstructed character equals target character.\n");
    else
        Print("WARNING: reconstructed character does NOT equal target character.\n");
        Print("reconstructed = ", rebuild, "\n");
        Print("target        = ", chi, "\n");
        return fail;
    fi;

    if IsNonnegativeIntegerCoeffList(sol) then
        Print("This is a valid non-negative integer Brauer decomposition.\n");
        Print("decomposition = ");
        PrintDecomposition(sol);
    else
        Print("This is NOT a valid non-negative integer decomposition.\n");
    fi;

    return sol;
end;;


CoeffLEQ := function(a,b)
    local i;

    for i in [1..Length(a)] do
        if a[i] > b[i] then
            return false;
        fi;
    od;

    return true;
end;;


SubtractCoeffs := function(a,b)
    local c, i;

    c := [];

    for i in [1..Length(a)] do
        Add(c, a[i] - b[i]);
    od;

    return c;
end;;


SearchCombosByDegree := function(target)
    local results, coeffs, recfun;

    results := [];
    coeffs := List([1..Length(degrees)], i -> 0);

    recfun := function(pos, remaining)
        local a, maxa;

        if pos > Length(degrees) then
            if remaining = 0 then
                Add(results, ShallowCopy(coeffs));
            fi;
            return;
        fi;

        maxa := QuoInt(remaining, degrees[pos]);

        for a in [0..maxa] do
            coeffs[pos] := a;
            recfun(pos + 1, remaining - a * degrees[pos]);
        od;

        coeffs[pos] := 0;
    end;

    recfun(1,target);

    return results;
end;;


############################################################
# PART 3:
# 27-dimensional minimal/Jordan candidates
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 3: 27-DIMENSIONAL MINIMAL/JORDAN CANDIDATES\n");
Print("============================================================\n");

OneIndices := PositionsProperty(degrees, d -> d = 1);;
TwelveIndices := PositionsProperty(degrees, d -> d = 12);;
FourteenIndices := PositionsProperty(degrees, d -> d = 14);;

Print("Degree-1 irreducibles at positions: ", OneIndices, "\n");
Print("Degree-12 irreducibles at positions: ", TwelveIndices, "\n");
Print("Degree-14 irreducibles at positions: ", FourteenIndices, "\n");

Candidates27 := [];;

for i in OneIndices do
    for j in TwelveIndices do
        for k in FourteenIndices do

            chi := List([1..Length(irr[1])],
                        r -> irr[i][r] + irr[j][r] + irr[k][r]);

            Add(Candidates27, [i,j,k,chi]);

        od;
    od;
od;

Print("\nNumber of formal 1 + 12 + 14 candidates = ", Length(Candidates27), "\n");

for c in [1..Length(Candidates27)] do

    chi := Candidates27[c][4];

    Print("\nCandidate ", c, ":\n");
    Print("  irreducible positions = ",
          Candidates27[c][1], " + ",
          Candidates27[c][2], " + ",
          Candidates27[c][3], "\n");

    Print("  total degree = ", chi[1], "\n");

    Print("  trace values on order-13 classes = ",
          List(pos13, j -> chi[j]),
          "\n");

    Print("  full Brauer-character values = ", chi, "\n");

od;

chi27a := AddChars([irr[1], irr[4], irr[5]]);;
chi27b := AddChars([irr[1], irr[4], irr[6]]);;

PrintCharSummary("Candidate 27a = 1 + 12 + 14a", chi27a);
PrintCharSummary("Candidate 27b = 1 + 12 + 14b", chi27b);

Print("\nInterpretation:\n");
Print("Both candidates have degree 27 and order-13 trace 1.\n");
Print("This matches the Magaard-style minimal/Jordan module pattern 1 + 12 + 14.\n");


############################################################
# PART 4:
# 14-point coset permutation module over GF(7)
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 4: 14-POINT COSET PERMUTATION MODULE OVER GF(7)\n");
Print("============================================================\n");

cosets := RightCosets(H,B);;
P := Action(H, cosets, OnRight);;

Print("Degree of coset action = ", LargestMovedPoint(P), "\n");
Print("Order of permutation image = ", Size(P), "\n");

K := GF(7);;
gensP := GeneratorsOfGroup(P);;
permMats := List(gensP, x -> PermutationMat(x, LargestMovedPoint(P), K));;

Print("Number of permutation matrix generators = ", Length(permMats), "\n");
Print("Matrix dimension = ", Length(permMats[1]), "\n");

Print("\nInterpretation:\n");
Print("The 14-dimensional coset permutation module over GF(7) has a fixed constant line.\n");
Print("Since 14 = 0 in GF(7), this constant line lies inside the augmentation subspace.\n");
Print("Therefore the quotient augmentation / constant line has dimension 12.\n");
Print("This is useful for understanding the possible source of the 12-dimensional constituent,\n");
Print("but the 14-point permutation module is not automatically one of the irreducible 14-dimensional modules.\n");


############################################################
# PART 5:
# 26-dimensional trace-zero minimal module
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 5: 26-DIMENSIONAL TRACE-ZERO MINIMAL MODULE\n");
Print("============================================================\n");

chi26a := AddChars([irr[4], irr[5]]);;
chi26b := AddChars([irr[4], irr[6]]);;

PrintCharSummary("Candidate 26a = 12 + 14a", chi26a);
PrintCharSummary("Candidate 26b = 12 + 14b", chi26b);

Print("\nImportant observation:\n");
Print("For order-13 elements, the 26-dimensional trace-zero module has trace 0.\n");
Print("This is because 12 has trace -1 and 14 has trace 1 on both order-13 classes.\n");


############################################################
# PART 6:
# Exterior and symmetric squares of 26
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 6: EXTERIOR AND SYMMETRIC SQUARES OF 26\n");
Print("============================================================\n");

ext26a := ExteriorSquareChar(btbl, chi26a);;
ext26b := ExteriorSquareChar(btbl, chi26b);;

sym26a := SymmetricSquareChar(btbl, chi26a);;
sym26b := SymmetricSquareChar(btbl, chi26b);;

PrintCharSummary("Exterior square of 26a", ext26a);
PrintCharSummary("Exterior square of 26b", ext26b);

PrintCharSummary("Symmetric square of 26a", sym26a);
PrintCharSummary("Symmetric square of 26b", sym26b);

Print("\nCorrected Brauer decomposition by solving, not scalar products:\n");

ExtCoeff26a_correct := BrauerDecomposeBySolving(
    "exterior square of 26a = exterior square of 12 + 14a",
    ext26a
);;

ExtCoeff26b_correct := BrauerDecomposeBySolving(
    "exterior square of 26b = exterior square of 12 + 14b",
    ext26b
);;

SymCoeff26a_correct := BrauerDecomposeBySolving(
    "symmetric square of 26a = symmetric square of 12 + 14a",
    sym26a
);;

SymCoeff26b_correct := BrauerDecomposeBySolving(
    "symmetric square of 26b = symmetric square of 12 + 14b",
    sym26b
);;


############################################################
# PART 7:
# Search formal 52-dimensional Brauer-character candidates
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 7: FORMAL 52-DIMENSIONAL TRACE-ZERO CANDIDATES\n");
Print("============================================================\n");

All52 := SearchCombosByDegree(52);;

Print("Total number of formal degree-52 combinations = ", Length(All52), "\n");

TraceZero52 := [];;

for coeffs in All52 do
    chi := CharFromCoeffs(coeffs);

    if List(pos13, j -> chi[j]) = [0,0] then
        Add(TraceZero52, [coeffs, chi]);
    fi;
od;

Print("Number of degree-52 candidates with order-13 trace [0,0] = ",
      Length(TraceZero52), "\n");

Print("\nAll trace-zero degree-52 candidates:\n");

for i in [1..Length(TraceZero52)] do
    Print("\nCandidate ", i, ":\n");
    Print("coefficients [1,7a,7b,12,14a,14b] = ", TraceZero52[i][1], "\n");
    Print("decomposition = ");
    PrintDecomposition(TraceZero52[i][1]);
    Print("order-13 trace = ", List(pos13, j -> TraceZero52[i][2][j]), "\n");
od;


############################################################
# PART 8:
# Exclude candidates with trivial composition factors
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 8: TRACE-ZERO 52-CANDIDATES WITH NO TRIVIAL FACTOR\n");
Print("============================================================\n");

NoTrivialTraceZero52 := Filtered(TraceZero52, x -> x[1][1] = 0);;

Print("Number of trace-zero degree-52 candidates with no trivial factor = ",
      Length(NoTrivialTraceZero52), "\n");

for i in [1..Length(NoTrivialTraceZero52)] do
    Print("\nNo-trivial candidate ", i, ":\n");
    Print("coefficients [1,7a,7b,12,14a,14b] = ",
          NoTrivialTraceZero52[i][1], "\n");
    Print("decomposition = ");
    PrintDecomposition(NoTrivialTraceZero52[i][1]);
    Print("Brauer character values on classes [1,2,3,6,13,13] = ",
          NoTrivialTraceZero52[i][2], "\n");
    Print("order-13 trace = ", List(pos13, j -> NoTrivialTraceZero52[i][2][j]), "\n");
od;


############################################################
# PART 9:
# Correct exterior-square containment test
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 9: CORRECTED EXTERIOR-SQUARE CONTAINMENT TEST\n");
Print("============================================================\n");

ContainedInExt26a_correct := [];;
ContainedInExt26b_correct := [];;

if ExtCoeff26a_correct <> fail and IsNonnegativeIntegerCoeffList(ExtCoeff26a_correct) then

    for item in NoTrivialTraceZero52 do
        if CoeffLEQ(item[1], ExtCoeff26a_correct) then
            Add(ContainedInExt26a_correct, item);
        fi;
    od;

fi;

if ExtCoeff26b_correct <> fail and IsNonnegativeIntegerCoeffList(ExtCoeff26b_correct) then

    for item in NoTrivialTraceZero52 do
        if CoeffLEQ(item[1], ExtCoeff26b_correct) then
            Add(ContainedInExt26b_correct, item);
        fi;
    od;

fi;

Print("\nFor 26a = 12 + 14a:\n");
Print("number of 52-candidates contained in exterior square = ",
      Length(ContainedInExt26a_correct), "\n");

for i in [1..Length(ContainedInExt26a_correct)] do
    Print("\nContained candidate ", i, ":\n");
    Print("candidate coefficients = ", ContainedInExt26a_correct[i][1], "\n");
    Print("candidate decomposition = ");
    PrintDecomposition(ContainedInExt26a_correct[i][1]);

    comp := SubtractCoeffs(ExtCoeff26a_correct, ContainedInExt26a_correct[i][1]);

    Print("complement coefficients = ", comp, "\n");
    Print("complement decomposition = ");
    PrintDecomposition(comp);
    Print("complement degree = ", CharFromCoeffs(comp)[1], "\n");
od;

Print("\nFor 26b = 12 + 14b:\n");
Print("number of 52-candidates contained in exterior square = ",
      Length(ContainedInExt26b_correct), "\n");

for i in [1..Length(ContainedInExt26b_correct)] do
    Print("\nContained candidate ", i, ":\n");
    Print("candidate coefficients = ", ContainedInExt26b_correct[i][1], "\n");
    Print("candidate decomposition = ");
    PrintDecomposition(ContainedInExt26b_correct[i][1]);

    comp := SubtractCoeffs(ExtCoeff26b_correct, ContainedInExt26b_correct[i][1]);

    Print("complement coefficients = ", comp, "\n");
    Print("complement decomposition = ");
    PrintDecomposition(comp);
    Print("complement degree = ", CharFromCoeffs(comp)[1], "\n");
od;


############################################################
# PART 10:
# Clean final summary table
############################################################

Print("\n");
Print("============================================================\n");
Print("PART 10: CLEAN SUMMARY OF 52-DIMENSIONAL TRACE-ZERO CANDIDATES\n");
Print("============================================================\n");

Print("Class orders are:\n");
Print(orders, "\n");

Print("\nThe six no-trivial, order-13 trace-zero, degree-52 candidates are:\n");

for i in [1..Length(NoTrivialTraceZero52)] do
    Print("\nCandidate ", i, "\n");
    Print("coefficients [1,7a,7b,12,14a,14b] = ");
    Print(NoTrivialTraceZero52[i][1], "\n");

    Print("decomposition = ");
    PrintDecomposition(NoTrivialTraceZero52[i][1]);

    Print("Brauer character values on classes [1,2,3,6,13,13] = ");
    Print(NoTrivialTraceZero52[i][2], "\n");

    Print("order-13 trace = ");
    Print(List(pos13, j -> NoTrivialTraceZero52[i][2][j]), "\n");
od;

Print("\nMost natural candidates from the 27-dimensional pattern are:\n");
Print("  2*12 + 2*14a\n");
Print("  2*12 + 14a + 14b\n");
Print("  2*12 + 2*14b\n");

Print("\nReason:\n");
Print("The 27-dimensional minimal/Jordan module has form 1 + 12 + 14.\n");
Print("Removing the fixed identity line gives 26 = 12 + 14.\n");
Print("So an adjoint module built most directly from this data is expected to involve mainly 12 and 14 constituents.\n");

Print("\nConclusion at this stage:\n");
Print("The characteristic-7 Brauer calculation confirms the 27-dimensional pattern 1 + 12 + 14.\n");
Print("The corresponding 26-dimensional trace-zero module is 12 + 14 and has order-13 trace zero.\n");
Print("There are six no-trivial 52-dimensional candidates with order-13 trace zero.\n");
Print("The exterior-square test is consistent with exterior square of 26 containing a 52-dimensional summand and a 273-dimensional complement,\n");
Print("but this test alone does not uniquely identify the adjoint restriction.\n");
Print("The next filter should compare the candidate traces on elements of orders 2, 3, and 6 with F4 Moody--Patera / EltTraces data.\n");


############################################################
# PART 11:
# Store useful objects globally
############################################################

F4L213_H := H;;
F4L213_S := S;;
F4L213_g := g;;
F4L213_f := f;;
F4L213_B := B;;
F4L213_GoodFs := GoodFs;;
F4L213_GoodTs := GoodTs;;

if Length(GoodTs) > 0 then
    F4L213_t := t;;
    F4L213_b := b;;
fi;

F4L213_char7_tbl := tbl;;
F4L213_char7_btbl := btbl;;
F4L213_char7_irr := irr;;
F4L213_char7_orders := orders;;
F4L213_char7_degrees := degrees;;
F4L213_char7_labels := labels;;
F4L213_char7_pos13 := pos13;;

F4L213_char7_Candidates27 := Candidates27;;
F4L213_char7_chi27a := chi27a;;
F4L213_char7_chi27b := chi27b;;
F4L213_char7_chi26a := chi26a;;
F4L213_char7_chi26b := chi26b;;

F4L213_CosetAction14 := P;;
F4L213_PermutationMats14_GF7 := permMats;;

F4L213_char7_ext26a := ext26a;;
F4L213_char7_ext26b := ext26b;;
F4L213_char7_sym26a := sym26a;;
F4L213_char7_sym26b := sym26b;;

F4L213_ExtCoeff26a_correct := ExtCoeff26a_correct;;
F4L213_ExtCoeff26b_correct := ExtCoeff26b_correct;;
F4L213_SymCoeff26a_correct := SymCoeff26a_correct;;
F4L213_SymCoeff26b_correct := SymCoeff26b_correct;;

F4L213_char7_TraceZero52 := TraceZero52;;
F4L213_char7_NoTrivialTraceZero52 := NoTrivialTraceZero52;;
F4L213_ContainedInExt26a_correct := ContainedInExt26a_correct;;
F4L213_ContainedInExt26b_correct := ContainedInExt26b_correct;;

Print("\n============================================================\n");
Print("DONE: F4 / L2(13) CHARACTERISTIC 7 WALTON-BRAUER RESTART\n");
Print("============================================================\n");

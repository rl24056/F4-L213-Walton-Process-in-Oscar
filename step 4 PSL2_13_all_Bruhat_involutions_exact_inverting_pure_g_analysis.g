############################################################
# PSL2(13) WALTON BRUHAT INVOLUTION ANALYSIS
#
# Purpose:
# 1. Build an abstract PSL2(13) model.
# 2. Choose g of order 13.
# 3. Choose f of order 6 such that <g,f> has order 78.
# 4. Enumerate all Bruhat-type involutions t such that:
#       Order(t)=2,
#       <g,f,t> = PSL2(13),
#       and Order(b*t)=3 for some b in B=<g,f>.
# 5. Check whether these t exactly invert the chosen f.
# 6. Focus on exact-inverting t.
# 7. Extract pure-g relations Order(g^k*t)=3.
#
# This script is designed to be pasted directly into GAP inside OSCAR.
############################################################


############################################################
# BASIC SETUP
############################################################

Print("\n============================================================\n");
Print("PSL2(13) WALTON BRUHAT INVOLUTION ANALYSIS\n");
Print("============================================================\n");

WT_H := PSL(2,13);;

Print("Order of WT_H = ", Size(WT_H), "\n");

WT_S := SylowSubgroup(WT_H,13);;
WT_g := GeneratorsOfGroup(WT_S)[1];;

if Order(WT_g) <> 13 then
    repeat
        WT_g := Random(WT_S);
    until Order(WT_g) = 13;
fi;

Print("Order of WT_S = ", Size(WT_S), "\n");
Print("Order of WT_g = ", Order(WT_g), "\n");

WT_N := Normalizer(WT_H,WT_S);;

Print("Order of N_H(<g>) = ", Size(WT_N), "\n");


############################################################
# HELPER FUNCTIONS
############################################################

WT_mult_order_mod := function(a,n)
    local x,k;

    if Gcd(a,n) <> 1 then
        return 0;
    fi;

    x := a mod n;
    k := 1;

    while x <> 1 do
        x := (x*a) mod n;
        k := k + 1;
    od;

    return k;
end;;

WT_actexp := function(x,g)
    local a, ord;

    ord := Order(g);

    for a in [0..ord-1] do
        if x*g*x^-1 = g^a then
            return a;
        fi;
    od;

    return fail;
end;;

WT_NormalizesCyclic := function(t,x)
    return (t*x*t^-1) in Group(x);
end;;

WT_ExactInverts := function(t,x)
    return t*x*t^-1 = x^-1;
end;;

WT_ActionExponentInCyclic := function(t,x)
    local e, ord;

    ord := Order(x);

    for e in [0..ord-1] do
        if t*x*t^-1 = x^e then
            return e;
        fi;
    od;

    return fail;
end;;

WT_check := function(name,x)
    Print("\n", name, "\n");
    Print("  Order = ", Order(x), "\n");
    Print("  Centralizer size in WT_H = ", Size(Centralizer(WT_H,x)), "\n");
    Print("  Conjugacy class size in WT_H = ",
          Size(WT_H)/Size(Centralizer(WT_H,x)), "\n");
end;;


############################################################
# CHOOSE f OF ORDER 6 WITH <g,f> = 13:6
############################################################

WT_GoodFs := [];;

for x in Elements(WT_N) do

    if Order(x) = 6 then

        WT_a := WT_actexp(x,WT_g);

        if WT_a <> fail and WT_mult_order_mod(WT_a,13) = 6
           and Size(Group(WT_g,x)) = 78 then

            Add(WT_GoodFs,x);

        fi;

    fi;

od;

Print("Number of suitable f-elements in N_H(<g>) = ",
      Length(WT_GoodFs), "\n");

if Length(WT_GoodFs) = 0 then
    Error("No suitable f found. Stop.");
fi;

WT_f := WT_GoodFs[1];;
WT_B := Group(WT_g,WT_f);;
WT_Belts := Elements(WT_B);;

Print("Chosen f has order = ", Order(WT_f), "\n");
Print("Action exponent of f on <g> = ", WT_actexp(WT_f,WT_g), "\n");
Print("Order of WT_B=<g,f> = ", Size(WT_B), "\n");


############################################################
# EXPRESS ELEMENTS OF B AS g^i*f^j
############################################################

WT_ExprInGF := function(x)
    local i,j;

    for i in [0..12] do
        for j in [0..5] do
            if WT_g^i * WT_f^j = x then
                return [i,j];
            fi;
        od;
    od;

    return fail;
end;;


############################################################
# STEP 1:
# Analyse all Bruhat-type involutions t in abstract PSL2(13)
############################################################

Print("\n============================================================\n");
Print("ANALYSIS OF ALL BRUHAT-TYPE INVOLUTIONS IN PSL2(13)\n");
Print("============================================================\n");

WT_AllBruhatData := [];;

WT_CountTotal := 0;;
WT_CountInvertF := 0;;
WT_CountNormalizeF := 0;;
WT_CountNormalizeG := 0;;
WT_CountMoveG := 0;;

for t0 in Elements(WT_H) do

    if Order(t0) = 2 and Size(Group(WT_g,WT_f,t0)) = Size(WT_H) then

        WT_BsForT := [];;

        for b0 in WT_Belts do
            if Order(b0*t0) = 3 then
                Add(WT_BsForT,b0);
            fi;
        od;

        if Length(WT_BsForT) > 0 then

            WT_CountTotal := WT_CountTotal + 1;;

            WT_invF := WT_ExactInverts(t0,WT_f);;
            WT_normF := WT_NormalizesCyclic(t0,WT_f);;
            WT_normG := WT_NormalizesCyclic(t0,WT_g);;

            if WT_invF then
                WT_CountInvertF := WT_CountInvertF + 1;;
            fi;

            if WT_normF then
                WT_CountNormalizeF := WT_CountNormalizeF + 1;;
            fi;

            if WT_normG then
                WT_CountNormalizeG := WT_CountNormalizeG + 1;;
            else
                WT_CountMoveG := WT_CountMoveG + 1;;
            fi;

            WT_expF := fail;;
            WT_expG := fail;;

            if WT_normF then
                WT_expF := WT_ActionExponentInCyclic(t0,WT_f);;
            fi;

            if WT_normG then
                WT_expG := WT_ActionExponentInCyclic(t0,WT_g);;
            fi;

            WT_bExprs := List(WT_BsForT, b0 -> WT_ExprInGF(b0));;

            Add(WT_AllBruhatData,
                rec(
                    t := t0,
                    numberOfB := Length(WT_BsForT),
                    firstB := WT_BsForT[1],
                    bExpressions := WT_bExprs,
                    exactInvertF := WT_invF,
                    normalizeF := WT_normF,
                    normalizeG := WT_normG,
                    actionExponentOnF := WT_expF,
                    actionExponentOnG := WT_expG
                )
            );;

        fi;

    fi;

od;

Print("Total Bruhat-type involutions found = ", WT_CountTotal, "\n");
Print("Number with t*f*t^-1 = f^-1 exactly = ", WT_CountInvertF, "\n");
Print("Number normalising <f> = ", WT_CountNormalizeF, "\n");
Print("Number normalising <g> = ", WT_CountNormalizeG, "\n");
Print("Number moving <g> outside itself = ", WT_CountMoveG, "\n");

Print("\nDistribution of number of b-elements per t with Order(b*t)=3:\n");
Print(Collected(List(WT_AllBruhatData, r -> r.numberOfB)), "\n");

Print("\nDistribution of whether t exactly inverts f:\n");
Print(Collected(List(WT_AllBruhatData, r -> r.exactInvertF)), "\n");

Print("\nDistribution of whether t normalises <f>:\n");
Print(Collected(List(WT_AllBruhatData, r -> r.normalizeF)), "\n");

Print("\nDistribution of action exponent on <f> when defined:\n");
Print(Collected(Filtered(List(WT_AllBruhatData,
      r -> r.actionExponentOnF), x -> x <> fail)), "\n");

Print("\nDistribution of whether t normalises <g>:\n");
Print(Collected(List(WT_AllBruhatData, r -> r.normalizeG)), "\n");

Print("\nFirst 10 Bruhat involution records:\n");

for i in [1..Minimum(10,Length(WT_AllBruhatData))] do

    r := WT_AllBruhatData[i];

    Print("\nRecord ", i, "\n");
    Print("number of b with Order(b*t)=3 = ", r.numberOfB, "\n");
    Print("first few b expressions [i,j] meaning g^i*f^j:\n");
    Print(r.bExpressions{[1..Minimum(10,Length(r.bExpressions))]}, "\n");
    Print("exactly inverts f? ", r.exactInvertF, "\n");
    Print("normalises <f>? ", r.normalizeF, "\n");
    Print("action exponent on <f> = ", r.actionExponentOnF, "\n");
    Print("normalises <g>? ", r.normalizeG, "\n");
    Print("action exponent on <g> = ", r.actionExponentOnG, "\n");

od;

WT_AllBExprs := Concatenation(List(WT_AllBruhatData,
                  r -> r.bExpressions));;

Print("\nDistribution of all b expressions [i,j] with b=g^i*f^j and Order(b*t)=3:\n");
Print(Collected(WT_AllBExprs), "\n");

Print("\nDistribution of the f-exponent j in b=g^i*f^j:\n");
Print(Collected(List(WT_AllBExprs, x -> x[2])), "\n");

Print("\n============================================================\n");
Print("SUMMARY OF STEP 1\n");
Print("============================================================\n");
Print("This tells us whether the abstract PSL2(13) Walton involution t really needs\n");
Print("to invert the exact chosen f, or only needs the weaker Bruhat relation\n");
Print("Order(b*t)=3 for some b in <g,f>.\n");
Print("If many Bruhat t do not exactly invert f, then the earlier F4 search condition\n");
Print("t*f*t^-1=f^-1 may have been too restrictive.\n");
Print("DONE BRUHAT INVOLUTION ANALYSIS.\n");


############################################################
# STEP 2:
# Focus only on exact-inverting Bruhat involutions
############################################################

Print("\n============================================================\n");
Print("EXACT-INVERTING BRUHAT INVOLUTIONS ONLY\n");
Print("============================================================\n");

WT_ExactInvertRecords :=
    Filtered(WT_AllBruhatData, r -> r.exactInvertF = true);;

Print("Number of Bruhat t with exact inversion of f = ",
      Length(WT_ExactInvertRecords), "\n");

if Length(WT_ExactInvertRecords) = 0 then

    Print("\nNo exact-inverting Bruhat involutions were found.\n");
    Print("So the strict condition t*f*t^-1=f^-1 fails for this chosen f.\n");

else

    Print("\nFor each exact-inverting t, list b=g^i*f^j with Order(b*t)=3:\n");

    for i in [1..Length(WT_ExactInvertRecords)] do

        r := WT_ExactInvertRecords[i];

        Print("\nExact-inverting record ", i, "\n");
        Print("number of b-elements = ", r.numberOfB, "\n");
        Print("b expressions [i,j] meaning g^i*f^j:\n");
        Print(r.bExpressions, "\n");
        Print("normalises <f>? ", r.normalizeF, "\n");
        Print("action exponent on <f> = ", r.actionExponentOnF, "\n");
        Print("normalises <g>? ", r.normalizeG, "\n");

    od;

    WT_ExactInvertBExprs :=
        Concatenation(List(WT_ExactInvertRecords, r -> r.bExpressions));;

    Print("\nDistribution of b expressions among exact-inverting t:\n");
    Print(Collected(WT_ExactInvertBExprs), "\n");

    Print("\nDistribution of f-exponent j in b=g^i*f^j among exact-inverting t:\n");
    Print(Collected(List(WT_ExactInvertBExprs, x -> x[2])), "\n");

    Print("\nDistribution of g-exponent i in b=g^i*f^j among exact-inverting t:\n");
    Print(Collected(List(WT_ExactInvertBExprs, x -> x[1])), "\n");

    Print("\nA compact usable abstract model is:\n");

    r := WT_ExactInvertRecords[1];;
    Print("Choose t = exact-inverting record 1.\n");
    Print("Then t has:\n");
    Print("  t*f*t^-1 = f^-1\n");
    Print("  t does not normalise <g>: ", not r.normalizeG, "\n");
    Print("  available b expressions = ", r.bExpressions, "\n");

    Print("\nTaking first b from this record:\n");
    WT_Model_t := r.t;;
    WT_Model_b := r.firstB;;
    WT_Model_b_expr := r.bExpressions[1];;

    Print("b expression [i,j] = ", WT_Model_b_expr, "\n");
    Print("Order of t = ", Order(WT_Model_t), "\n");
    Print("Order of b*t = ", Order(WT_Model_b*WT_Model_t), "\n");
    Print("Order of <g,f,t> = ",
          Size(Group(WT_g,WT_f,WT_Model_t)), "\n");

    Print("\nBasic checks for this stricter model:\n");
    WT_check("g", WT_g);
    WT_check("f", WT_f);
    WT_check("t exact-inverting f", WT_Model_t);
    WT_check("b*t for exact-inverting t", WT_Model_b*WT_Model_t);

    Print("\n============================================================\n");
    Print("SUMMARY OF STEP 2\n");
    Print("============================================================\n");
    Print("The exact-inverting version of the abstract Walton model exists.\n");
    Print("This means the previous F4 search condition t*f*t^-1=f^-1 is not impossible.\n");
    Print("But it only captures a small special subset of all Bruhat-type t's.\n");
    Print("The next F4-side search should therefore record two layers:\n");
    Print("  Layer 1: exact-inverting t, matching Walton strictly.\n");
    Print("  Layer 2: all Bruhat-style t with Order(b*t)=3, matching PSL2 more generally.\n");
    Print("DONE EXACT-INVERTING ANALYSIS.\n");

fi;


############################################################
# STEP 3:
# Extract pure-g Bruhat relations among exact-inverting t's
############################################################

Print("\n============================================================\n");
Print("PURE-g BRUHAT RELATIONS FOR EXACT-INVERTING t\n");
Print("============================================================\n");

WT_PureGBruhatData := [];;

if Length(WT_ExactInvertRecords) = 0 then

    Print("No exact-inverting records exist, so no pure-g test is possible.\n");

else

    for i in [1..Length(WT_ExactInvertRecords)] do

        r := WT_ExactInvertRecords[i];

        purePairs := Filtered(r.bExpressions, pair -> pair[2] = 0);
        pureK := List(purePairs, pair -> pair[1]);

        Print("\nExact-inverting record ", i, "\n");
        Print("pure-g pairs [k,0] = ", purePairs, "\n");
        Print("pure-g exponents k with Order(g^k*t)=3 = ", pureK, "\n");

        for k in pureK do
            Print("  k = ", k,
                  " | Order(g^k*t) = ", Order((WT_g^k)*r.t),
                  " | Order(<g,f,t>) = ", Size(Group(WT_g,WT_f,r.t)),
                  "\n");
        od;

        Add(WT_PureGBruhatData,
            rec(
                recordNumber := i,
                t := r.t,
                purePairs := purePairs,
                pureK := pureK
            )
        );

    od;

    WT_AllPureK := Concatenation(List(WT_PureGBruhatData,
                     r -> r.pureK));;

    Print("\nDistribution of pure-g exponents k:\n");
    Print(Collected(WT_AllPureK), "\n");

    Print("\nTotal number of pure-g Bruhat relations = ",
          Length(WT_AllPureK), "\n");

    WT_PureGNonEmpty :=
        Filtered(WT_PureGBruhatData, r -> Length(r.pureK) > 0);;

    if Length(WT_PureGNonEmpty) = 0 then

        Print("\nNo pure-g relation exists among the exact-inverting records.\n");
        Print("So one must use a general b=g^i*f^j rather than b=g^k only.\n");

    else

        Print("\nNow choose the first exact-inverting model with a pure-g relation.\n");

        WT_StrictPure_Record := WT_PureGNonEmpty[1];;
        WT_StrictPure_t := WT_StrictPure_Record.t;;
        WT_StrictPure_k := WT_StrictPure_Record.pureK[1];;

        Print("Chosen exact-inverting record = ",
              WT_StrictPure_Record.recordNumber, "\n");
        Print("Chosen k = ", WT_StrictPure_k, "\n");
        Print("So the clean Bruhat relation is Order(g^k*t)=3.\n");

        Print("\nVerification of strict pure-g Walton model:\n");
        Print("Order of g = ", Order(WT_g), "\n");
        Print("Order of f = ", Order(WT_f), "\n");
        Print("Order of t = ", Order(WT_StrictPure_t), "\n");
        Print("Action exponent of f on <g> = ",
              WT_actexp(WT_f,WT_g), "\n");
        Print("t*f*t^-1 = f^-1 ? ",
              WT_StrictPure_t*WT_f*WT_StrictPure_t^-1 = WT_f^-1, "\n");
        Print("t normalises <g> ? ",
              WT_NormalizesCyclic(WT_StrictPure_t,WT_g), "\n");
        Print("Order(g^k*t) = ",
              Order((WT_g^WT_StrictPure_k)*WT_StrictPure_t), "\n");
        Print("Order of <g,f> = ", Size(Group(WT_g,WT_f)), "\n");
        Print("Order of <g,f,t> = ",
              Size(Group(WT_g,WT_f,WT_StrictPure_t)), "\n");

        Print("\nBasic checks for strict pure-g model:\n");
        WT_check("g", WT_g);
        WT_check("f", WT_f);
        WT_check("t", WT_StrictPure_t);
        WT_check("g^k*t", (WT_g^WT_StrictPure_k)*WT_StrictPure_t);

        Print("\n============================================================\n");
        Print("SUMMARY OF STEP 3\n");
        Print("============================================================\n");
        Print("The strict Walton model can be made even cleaner:\n");
        Print("Instead of requiring a general b in <g,f>, we can choose b = g^k.\n");
        Print("For the chosen model, k = ", WT_StrictPure_k, ".\n");
        Print("Thus the F4-side strict search can test:\n");
        Print("  Order(t)=2,\n");
        Print("  t*f*t^-1=f^-1,\n");
        Print("  t does not normalise <g>,\n");
        Print("  and Order(g^k*t)=3 for some k in [1..12].\n");
        Print("DONE PURE-g BRUHAT RELATION STEP.\n");

    fi;

fi;


############################################################
# FINAL SUMMARY
############################################################

Print("\n============================================================\n");
Print("FINAL SCRIPT SUMMARY\n");
Print("============================================================\n");
Print("This file gives the abstract PSL2(13) benchmark for the F4 search.\n");
Print("It separates three levels:\n");
Print("1. All Bruhat-type involutions satisfying Order(b*t)=3 for some b in <g,f>.\n");
Print("2. The smaller subset where t exactly inverts the chosen f.\n");
Print("3. The stricter pure-g subset where b can be chosen as g^k.\n");
Print("These outputs can be used to decide whether the F4-side search condition\n");
Print("t*f*t^-1=f^-1 is too strict, or whether it is still a valid strict Walton model.\n");
Print("DONE FULL PSL2(13) BRUHAT INVOLUTION ANALYSIS.\n");
Print("============================================================\n");

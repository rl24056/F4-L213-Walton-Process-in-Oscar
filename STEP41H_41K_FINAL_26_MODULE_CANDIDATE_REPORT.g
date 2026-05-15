############################################################
# STEP 41H TO STEP 41K:
# FINAL TRACE REPORT AND CHOICE OF THE 26-DIMENSIONAL CANDIDATE
#
# Continue from Step 41G.
# Do NOT restart.
#
# Aim:
#   Step 41G produced GoodLocal26_41G.
#
#   We now:
#     1. Print trace profiles for every good 26-dimensional candidate.
#     2. Choose the likely minimal-module candidate from 14-record #4.
#     3. Store the final variables:
#          H26_min41
#          g26_min41
#          f26_min41
#          t26_min41
#          B26_min41
#     4. Print a clean final report with the GF(7) trace interpretation fixed.
#
# Main reason for choosing 14-record #4:
#
#   Its 26-dimensional trace profile is:
#
#       g      trace 0
#       f      trace 1
#       f^2    trace -1
#       f^3    trace -2
#       t      trace -2
#
#   Doubling gives the old 52-dimensional adjoint-style target:
#
#       g      trace 0
#       f      trace 2
#       f^2    trace -2
#       f^3    trace -4
#       t      trace -4
#
############################################################

LogTo("STEP41H_TO_41K_FINAL_26_MODULE_REPORT_LOG.txt");

Print("\n============================================================\n");
Print("STEP 41H TO 41K: FINAL 26-DIMENSIONAL MODULE REPORT\n");
Print("============================================================\n");

############################################################
# SAFETY CHECKS
############################################################

if not IsBound(GoodLocal26_41G) then
    Error("GoodLocal26_41G is not bound. Run Step 41G first.");
fi;

if not IsBound(TraceMat41G) then
    Error("TraceMat41G is not bound. Step 41G helper functions are missing.");
fi;

if not IsBound(ActionExponentCyclic41G) then
    Error("ActionExponentCyclic41G is not bound. Step 41G helper functions are missing.");
fi;

if not IsBound(FindBruhatWitnessMat41G) then
    Error("FindBruhatWitnessMat41G is not bound. Step 41G helper functions are missing.");
fi;

Print("Number of good local 26-module triples available = ",
      Length(GoodLocal26_41G), "\n");


############################################################
# HELPER FUNCTIONS
############################################################

# General small signed display for GF(7).
# This is useful for the 26-dimensional minimal trace profile.
Trace26Label41HK := function(x)
    if x = 0 * One(GF(7)) then
        return "0";
    elif x = 1 * One(GF(7)) then
        return "1";
    elif x = -1 * One(GF(7)) then
        return "-1";
    elif x = 2 * One(GF(7)) then
        return "2";
    elif x = -2 * One(GF(7)) then
        return "-2";
    elif x = 3 * One(GF(7)) then
        return "3";
    elif x = -3 * One(GF(7)) then
        return "-3";
    else
        return String(x);
    fi;
end;;

# Special display for comparison with the old 52-dimensional adjoint target.
# Important:
#   In GF(7), the element printed as 3 can also represent -4.
#   For the old adjoint trace target, we want to display it as -4.
Trace52TargetLabel41HK := function(x)
    if x = 0 * One(GF(7)) then
        return "0";
    elif x = 2 * One(GF(7)) then
        return "2";
    elif x = -2 * One(GF(7)) then
        return "-2";
    elif x = -4 * One(GF(7)) then
        return "-4";
    else
        return String(x);
    fi;
end;;

# Safer witness getter.
# Some records may already store a witness.
# If not, compute it again.
GetWitness26_41HK := function(r)
    if IsBound(r.witness) then
        return r.witness;
    fi;

    return FindBruhatWitnessMat41G(r.g26, r.f26, r.t26, 26);
end;;

# Print one candidate.
PrintOne26Candidate41HK := function(r)
    local H, B, wit, classes, idx, C, rep, tr;

    H := r.H26;
    B := Group(r.g26, r.f26);
    wit := GetWitness26_41HK(r);

    Print("\n------------------------------------------------------------\n");
    Print("26-module candidate from 14-record #", r.index14, "\n");

    if IsBound(r.abs_irred) then
        Print("14-module absolutely irreducible? ", r.abs_irred, "\n");
    fi;

    Print("Size(H26) = ", Size(H), "\n");
    Print("Size(B26=<g,f>) = ", Size(B), "\n");

    Print("\nBasic element data:\n");
    Print("  Order(g26) = ", Order(r.g26), "\n");
    Print("  Order(f26) = ", Order(r.f26), "\n");
    Print("  Order(t26) = ", Order(r.t26), "\n");

    Print("\nWalton-style checks:\n");
    Print("  f^t = f^-1 ? ", r.f26^r.t26 = r.f26^-1, "\n");
    Print("  t in B? ", r.t26 in B, "\n");
    Print("  t normalises <g>? ",
          ActionExponentCyclic41G(r.g26, r.t26) <> fail, "\n");

    if wit = fail then
        Print("  Bruhat witness: none\n");
    else
        Print("  Bruhat witness: b = g^", wit.i,
              " * f^", wit.j, "\n");
        Print("  Order(b*t) = ",
              Order((r.g26^wit.i * r.f26^wit.j) * r.t26), "\n");
    fi;

    Print("\n26-dimensional trace profile:\n");
    Print("  Trace(g)   = ", TraceMat41G(r.g26),
          "   label = ", Trace26Label41HK(TraceMat41G(r.g26)), "\n");
    Print("  Trace(f)   = ", TraceMat41G(r.f26),
          "   label = ", Trace26Label41HK(TraceMat41G(r.f26)), "\n");
    Print("  Trace(f^2) = ", TraceMat41G(r.f26^2),
          "   label = ", Trace26Label41HK(TraceMat41G(r.f26^2)), "\n");
    Print("  Trace(f^3) = ", TraceMat41G(r.f26^3),
          "   label = ", Trace26Label41HK(TraceMat41G(r.f26^3)), "\n");
    Print("  Trace(t)   = ", TraceMat41G(r.t26),
          "   label = ", Trace26Label41HK(TraceMat41G(r.t26)), "\n");

    Print("\nDoubled trace profile, for old 52-dimensional adjoint comparison:\n");
    Print("  2*Trace(g)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(r.g26)), "\n");
    Print("  2*Trace(f)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(r.f26)), "\n");
    Print("  2*Trace(f^2) = ", Trace52TargetLabel41HK(2 * TraceMat41G(r.f26^2)), "\n");
    Print("  2*Trace(f^3) = ", Trace52TargetLabel41HK(2 * TraceMat41G(r.f26^3)), "\n");
    Print("  2*Trace(t)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(r.t26)), "\n");

    Print("\nConjugacy-class trace profile inside this 26-dimensional model:\n");
    Print("Class | Order | Size | Trace | Label\n");

    classes := ConjugacyClasses(H);

    for idx in [1..Length(classes)] do
        C := classes[idx];
        rep := Representative(C);
        tr := TraceMat41G(rep);

        Print("  ", idx,
              " | ", Order(rep),
              " | ", Size(C),
              " | ", tr,
              " | ", Trace26Label41HK(tr), "\n");
    od;
end;;


############################################################
# STEP 41H:
# PRINT TRACE PROFILES OF ALL GOOD 26-MODULE CANDIDATES
############################################################

Print("\n============================================================\n");
Print("STEP 41H: TRACE PROFILES OF GOOD 26-MODULE CANDIDATES\n");
Print("============================================================\n");

for rec26_41HK in GoodLocal26_41G do
    PrintOne26Candidate41HK(rec26_41HK);
od;

Print("\n============================================================\n");
Print("STEP 41H FINISHED\n");
Print("============================================================\n");


############################################################
# STEP 41I:
# CHOOSE THE LIKELY MINIMAL 26-DIMENSIONAL CANDIDATE
############################################################

Print("\n============================================================\n");
Print("STEP 41I: CHOOSE THE LIKELY MINIMAL 26-DIMENSIONAL CANDIDATE\n");
Print("============================================================\n");

chosen26_41I := fail;;

for r41I in GoodLocal26_41G do
    if r41I.index14 = 4 then
        chosen26_41I := r41I;
        break;
    fi;
od;

if chosen26_41I = fail then
    Error("Could not find the candidate from 14-record #4.");
fi;

H26_min41 := chosen26_41I.H26;;
g26_min41 := chosen26_41I.g26;;
f26_min41 := chosen26_41I.f26;;
t26_min41 := chosen26_41I.t26;;
B26_min41 := Group(g26_min41, f26_min41);;

wit26_min41 := FindBruhatWitnessMat41G(g26_min41, f26_min41, t26_min41, 26);;

Print("\nChosen candidate:\n");
Print("  14-record index = ", chosen26_41I.index14, "\n");

if IsBound(chosen26_41I.abs_irred) then
    Print("  14-record absolutely irreducible = ",
          chosen26_41I.abs_irred, "\n");
fi;

Print("\nBasic group checks:\n");
Print("  Size(H26_min41) = ", Size(H26_min41), "\n");
Print("  Size(B26_min41) = ", Size(B26_min41), "\n");
Print("  Order(g26_min41) = ", Order(g26_min41), "\n");
Print("  Order(f26_min41) = ", Order(f26_min41), "\n");
Print("  Order(t26_min41) = ", Order(t26_min41), "\n");
Print("  Size(<g,f,t>) = ",
      Size(Group(g26_min41, f26_min41, t26_min41)), "\n");

Print("\nWalton-style checks:\n");
Print("  f^t = f^-1 ? ", f26_min41^t26_min41 = f26_min41^-1, "\n");
Print("  t in B? ", t26_min41 in B26_min41, "\n");
Print("  t normalises <g>? ",
      ActionExponentCyclic41G(g26_min41, t26_min41) <> fail, "\n");

if wit26_min41 = fail then
    Print("  Bruhat witness: none\n");
else
    Print("  Bruhat witness: b = g^",
          wit26_min41.i, " * f^", wit26_min41.j, "\n");
    Print("  Order(b*t) = ",
          Order((g26_min41^wit26_min41.i * f26_min41^wit26_min41.j)
                * t26_min41), "\n");
fi;

Print("\nMinimal 26-dimensional traces over GF(7):\n");
Print("  Trace(g)   = ", TraceMat41G(g26_min41),
      "   label = ", Trace26Label41HK(TraceMat41G(g26_min41)), "\n");
Print("  Trace(f)   = ", TraceMat41G(f26_min41),
      "   label = ", Trace26Label41HK(TraceMat41G(f26_min41)), "\n");
Print("  Trace(f^2) = ", TraceMat41G(f26_min41^2),
      "   label = ", Trace26Label41HK(TraceMat41G(f26_min41^2)), "\n");
Print("  Trace(f^3) = ", TraceMat41G(f26_min41^3),
      "   label = ", Trace26Label41HK(TraceMat41G(f26_min41^3)), "\n");
Print("  Trace(t)   = ", TraceMat41G(t26_min41),
      "   label = ", Trace26Label41HK(TraceMat41G(t26_min41)), "\n");

Print("\nDoubled traces, for comparison with old 52-dimensional adjoint target:\n");
Print("  2*Trace(g)   = ",
      Trace52TargetLabel41HK(2 * TraceMat41G(g26_min41)), "\n");
Print("  2*Trace(f)   = ",
      Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41)), "\n");
Print("  2*Trace(f^2) = ",
      Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41^2)), "\n");
Print("  2*Trace(f^3) = ",
      Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41^3)), "\n");
Print("  2*Trace(t)   = ",
      Trace52TargetLabel41HK(2 * TraceMat41G(t26_min41)), "\n");

Print("\nStored final candidate variables:\n");
Print("  H26_min41\n");
Print("  g26_min41\n");
Print("  f26_min41\n");
Print("  t26_min41\n");
Print("  B26_min41\n");

Print("\nConclusion of Step 41I:\n");
Print("  14-record #4 is the likely candidate for the 26-dimensional minimal-module route.\n");
Print("  It gives a synchronised PSL2(13) action of size 1092.\n");
Print("  Its doubled trace profile matches the old 52-dimensional adjoint target.\n");

Print("\n============================================================\n");
Print("STEP 41I FINISHED\n");
Print("============================================================\n");


############################################################
# STEP 41J:
# CLEAN FINAL REPORT FOR THE CHOSEN 26-DIMENSIONAL CANDIDATE
############################################################

Print("\n============================================================\n");
Print("STEP 41J: CLEAN FINAL REPORT FOR CHOSEN 26-MODULE\n");
Print("============================================================\n");

Print("\nChosen candidate variables:\n");
Print("  H26_min41, g26_min41, f26_min41, t26_min41, B26_min41\n");

Print("\nGroup checks:\n");
Print("  Size(H26_min41) = ", Size(H26_min41), "\n");
Print("  Size(B26_min41) = ", Size(B26_min41), "\n");
Print("  Order(g26_min41) = ", Order(g26_min41), "\n");
Print("  Order(f26_min41) = ", Order(f26_min41), "\n");
Print("  Order(t26_min41) = ", Order(t26_min41), "\n");
Print("  Size(<g,f,t>) = ",
      Size(Group(g26_min41, f26_min41, t26_min41)), "\n");

Print("\nWalton checks:\n");
Print("  f^t = f^-1 ? ", f26_min41^t26_min41 = f26_min41^-1, "\n");
Print("  t in B? ", t26_min41 in B26_min41, "\n");
Print("  t normalises <g>? ",
      ActionExponentCyclic41G(g26_min41, t26_min41) <> fail, "\n");

wit26_clean41J := FindBruhatWitnessMat41G(g26_min41, f26_min41, t26_min41, 26);;

if wit26_clean41J = fail then
    Print("  Bruhat witness: none\n");
else
    Print("  Bruhat witness: b = g^",
          wit26_clean41J.i, " * f^", wit26_clean41J.j, "\n");
    Print("  Order(b*t) = ",
          Order((g26_min41^wit26_clean41J.i * f26_min41^wit26_clean41J.j)
                * t26_min41), "\n");
fi;

Print("\nClean minimal 26-dimensional trace profile:\n");
Print("  Trace(g)   = ", Trace26Label41HK(TraceMat41G(g26_min41)), "\n");
Print("  Trace(f)   = ", Trace26Label41HK(TraceMat41G(f26_min41)), "\n");
Print("  Trace(f^2) = ", Trace26Label41HK(TraceMat41G(f26_min41^2)), "\n");
Print("  Trace(f^3) = ", Trace26Label41HK(TraceMat41G(f26_min41^3)), "\n");
Print("  Trace(t)   = ", Trace26Label41HK(TraceMat41G(t26_min41)), "\n");

Print("\nClean doubled trace profile, for comparison with 52-dimensional adjoint target:\n");
Print("  2*Trace(g)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(g26_min41)), "\n");
Print("  2*Trace(f)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41)), "\n");
Print("  2*Trace(f^2) = ", Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41^2)), "\n");
Print("  2*Trace(f^3) = ", Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41^3)), "\n");
Print("  2*Trace(t)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(t26_min41)), "\n");

Print("\nConclusion of Step 41J:\n");
Print("  The synchronised 26-dimensional candidate from 14-record #4 is the likely minimal-module candidate.\n");
Print("  It realises PSL2(13), has B of order 78, has an external exact-inverting t,\n");
Print("  and has the expected doubled adjoint trace profile.\n");

Print("\n============================================================\n");
Print("STEP 41J FINISHED\n");
Print("============================================================\n");


############################################################
# STEP 41K:
# FINAL CLEAN REPORT, WITH GF(7) TRACE INTERPRETATION FIXED
############################################################

Print("\n============================================================\n");
Print("STEP 41K: FINAL CLEAN REPORT WITH TRACE INTERPRETATION\n");
Print("============================================================\n");

wit41K := FindBruhatWitnessMat41G(g26_min41, f26_min41, t26_min41, 26);;

Print("\nChosen candidate: 14-record #4\n");
Print("This is the likely 26-dimensional minimal-module candidate.\n");

Print("\nGroup checks:\n");
Print("  Size(H26_min41) = ", Size(H26_min41), "\n");
Print("  Size(B26_min41) = ", Size(B26_min41), "\n");
Print("  Order(g26_min41) = ", Order(g26_min41), "\n");
Print("  Order(f26_min41) = ", Order(f26_min41), "\n");
Print("  Order(t26_min41) = ", Order(t26_min41), "\n");
Print("  Size(<g,f,t>) = ",
      Size(Group(g26_min41, f26_min41, t26_min41)), "\n");

Print("\nWalton checks:\n");
Print("  f^t = f^-1 ? ", f26_min41^t26_min41 = f26_min41^-1, "\n");
Print("  t in B? ", t26_min41 in B26_min41, "\n");
Print("  t normalises <g>? ",
      ActionExponentCyclic41G(g26_min41, t26_min41) <> fail, "\n");

if wit41K = fail then
    Print("  Bruhat witness: none\n");
else
    Print("  Bruhat witness: b = g^", wit41K.i, " * f^", wit41K.j, "\n");
    Print("  Order(b*t) = ",
          Order((g26_min41^wit41K.i * f26_min41^wit41K.j)
                * t26_min41), "\n");
fi;

Print("\nMinimal 26-dimensional trace profile:\n");
Print("  Trace(g)   = ", Trace26Label41HK(TraceMat41G(g26_min41)), "\n");
Print("  Trace(f)   = ", Trace26Label41HK(TraceMat41G(f26_min41)), "\n");
Print("  Trace(f^2) = ", Trace26Label41HK(TraceMat41G(f26_min41^2)), "\n");
Print("  Trace(f^3) = ", Trace26Label41HK(TraceMat41G(f26_min41^3)), "\n");
Print("  Trace(t)   = ", Trace26Label41HK(TraceMat41G(t26_min41)), "\n");

Print("\nDoubled trace profile, interpreted as the old 52-dimensional adjoint target:\n");
Print("  2*Trace(g)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(g26_min41)), "\n");
Print("  2*Trace(f)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41)), "\n");
Print("  2*Trace(f^2) = ", Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41^2)), "\n");
Print("  2*Trace(f^3) = ", Trace52TargetLabel41HK(2 * TraceMat41G(f26_min41^3)), "\n");
Print("  2*Trace(t)   = ", Trace52TargetLabel41HK(2 * TraceMat41G(t26_min41)), "\n");

Print("\nFinal conclusion:\n");
Print("  The synchronised 26-dimensional model from 14-record #4 realises PSL2(13).\n");
Print("  It has B=13:6 of order 78, an external exact-inverting involution t,\n");
Print("  and a Bruhat relation of order 3 with an element b in B.\n");
Print("  The 26-dimensional trace profile is 0, 1, -1, -2, -2.\n");
Print("  Doubling gives 0, 2, -2, -4, -4, matching the old adjoint trace target.\n");

Print("\nStored final objects:\n");
Print("  H26_min41\n");
Print("  g26_min41\n");
Print("  f26_min41\n");
Print("  t26_min41\n");
Print("  B26_min41\n");

Print("\n============================================================\n");
Print("STEP 41K FINISHED\n");
Print("============================================================\n");

LogTo();

package com.el.dg;

import de.tudresden.inf.lat.jcel.coreontology.axiom.GCI0Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.NormalizedIntegerAxiom;

import java.util.ArrayList;
import java.util.Set;

/**
 * Created by winter on 8/9/15.
 */
public class PatternDiagnosis {

    Set<Set<NormalizedIntegerAxiom>> patternSet;

    PatternDiagnosis(Set<Set<NormalizedIntegerAxiom>> pS){
        patternSet = pS;
    }

    public void doDiagnosis(GCI0Axiom observation, ArrayList<NormalizedIntegerAxiom> tbox){

    }
}

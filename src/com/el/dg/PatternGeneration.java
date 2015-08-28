package com.el.dg;

import de.tudresden.inf.lat.jcel.coreontology.axiom.NormalizedIntegerAxiom;
import de.tudresden.inf.lat.jcel.owlapi.main.JcelReasoner;
import de.tudresden.inf.lat.jcel.owlapi.translator.TranslationRepository;
import de.tudresden.inf.lat.jcel.reasoner.main.RuleBasedReasoner;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;

import java.util.Map;
import java.util.Set;

/**
 * Created by winter on 28/8/15.
 */
public class PatternGeneration {
    private Set<NormalizedIntegerAxiom> tbox;
    private OWLOntology ontology;

    private Set<Set<NormalizedIntegerAxiom>> S;
    private Set<Set<NormalizedIntegerAxiom>> S_v;
    private Set<Set<NormalizedIntegerAxiom>> S_a;

    private Map<Integer, OWLClass> classMap;
    private Map<Integer, OWLObjectProperty> propMap;

    public PatternGeneration(OWLOntology ont){
        ontology = ont;
    }

    public void doGenerate(){
        doPretreatment();

    }

    /* normalize and get class, property map*/
    private void doPretreatment(){
        JcelReasoner reasoner = new JcelReasoner(ontology, false);
        RuleBasedReasoner ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();

        TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();
        classMap = translatorReposity.getClassMap();
        propMap = translatorReposity.getObjectPropertyMap();
        tbox = ruleBasedReasoner.getNormalizedIntegerAxiomSet();
    }


}

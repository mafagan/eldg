package com.el.dg;

import de.tudresden.inf.lat.jcel.coreontology.axiom.*;
import de.tudresden.inf.lat.jcel.ontology.axiom.complex.ComplexIntegerAxiom;
import de.tudresden.inf.lat.jcel.ontology.axiom.complex.ComplexIntegerAxiomFactoryImpl;
import de.tudresden.inf.lat.jcel.ontology.datatype.IntegerClass;
import de.tudresden.inf.lat.jcel.ontology.datatype.IntegerDataTypeFactoryImpl;
import de.tudresden.inf.lat.jcel.owlapi.main.JcelReasoner;
import de.tudresden.inf.lat.jcel.owlapi.translator.TranslationRepository;
import de.tudresden.inf.lat.jcel.reasoner.main.RuleBasedReasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.util.*;

/**
 * Created by winter on 8/9/15.
 */
public class PatternDiagnosis {

    Set<Set<NormalizedIntegerAxiom>> patternSet;
    OWLOntologyManager manager;
    OWLDataFactory dataFactory;

    IntegerDataTypeFactoryImpl axiomFat;
    ComplexIntegerAxiomFactoryImpl cpFat;

    PatternDiagnosis(Set<Set<NormalizedIntegerAxiom>> pS){
        patternSet = pS;

        manager = OWLManager.createOWLOntologyManager();
        axiomFat = new IntegerDataTypeFactoryImpl();
        cpFat = new ComplexIntegerAxiomFactoryImpl();
    }

    public void doDiagnosis(GCI0Axiom observation, ArrayList<NormalizedIntegerAxiom> tbox){

    }

    private boolean isEntailed(Set<NormalizedIntegerAxiom> tbox, NormalizedIntegerAxiom axiom) throws OWLOntologyCreationException {
        String prefix = "danye://";
        IRI ontologyIRI = IRI.create(prefix);
        OWLOntology ontology = manager.createOntology(ontologyIRI);
        
        Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();

        Iterator<NormalizedIntegerAxiom> tboxIt = tbox.iterator();
        while (tboxIt.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = tboxIt.next();

            if (tmpAxiom instanceof GCI0Axiom){

                GCI0Axiom tmpAx = (GCI0Axiom) tmpAxiom;
                OWLClass subClass = dataFactory.getOWLClass(IRI.create(prefix+tmpAx.getSubClass()));
                OWLClass supClass = dataFactory.getOWLClass(IRI.create(prefix+tmpAx.getSubClass()));
                axioms.add(dataFactory.getOWLSubClassOfAxiom(subClass, supClass));

            } else if (tmpAxiom instanceof GCI1Axiom){

                GCI1Axiom tmpAx = (GCI1Axiom) tmpAxiom;
                OWLClass leftSubClass = dataFactory.getOWLClass(IRI.create(prefix+tmpAx.getLeftSubClass()));
                OWLClass rightSubClass = dataFactory.getOWLClass(IRI.create(prefix + tmpAx.getRightSubClass()));
                OWLObjectIntersectionOf obj = dataFactory.getOWLObjectIntersectionOf(leftSubClass, rightSubClass);
                OWLClass supClass = dataFactory.getOWLClass(IRI.create(prefix+tmpAx.getSuperClass()));
                axioms.add(dataFactory.getOWLSubClassOfAxiom(obj, supClass));

            } else if (tmpAxiom instanceof GCI2Axiom){

                GCI2Axiom tmpAx = (GCI2Axiom) tmpAxiom;
                OWLClass subClass = dataFactory.getOWLClass(IRI.create(prefix+tmpAx.getSubClass()));
                OWLObjectProperty property = dataFactory.getOWLObjectProperty(IRI.create(prefix + tmpAx.getPropertyInSuperClass()));
                OWLClass rightSupClass = dataFactory.getOWLClass(IRI.create(prefix + tmpAx.getClassInSuperClass()));
                OWLObjectSomeValuesFrom objExist = dataFactory.getOWLObjectSomeValuesFrom(property, rightSupClass);
                axioms.add(dataFactory.getOWLSubClassOfAxiom(subClass, objExist));

            } else if (tmpAxiom instanceof GCI3Axiom){

                GCI3Axiom tmpAx = (GCI3Axiom) tmpAxiom;
                OWLObjectProperty property = dataFactory.getOWLObjectProperty(IRI.create(prefix+tmpAx.getPropertyInSubClass()));
                OWLClass leftSubClass = dataFactory.getOWLClass(IRI.create(prefix + tmpAx.getClassInSubClass()));
                OWLClass supClass = dataFactory.getOWLClass(IRI.create(prefix+tmpAx.getSuperClass()));
                OWLObjectSomeValuesFrom objExist = dataFactory.getOWLObjectSomeValuesFrom(property, leftSubClass);
                axioms.add(dataFactory.getOWLSubClassOfAxiom(objExist, supClass));
            } else if (tmpAxiom instanceof RI2Axiom){

                RI2Axiom tmpAx = (RI2Axiom) tmpAxiom;
                OWLObjectProperty subProperty = dataFactory.getOWLObjectProperty(IRI.create(prefix+tmpAx.getSubProperty()));
                OWLObjectProperty supProperty = dataFactory.getOWLObjectProperty(IRI.create(prefix+tmpAx.getSuperProperty()));
                axioms.add(dataFactory.getOWLSubObjectPropertyOfAxiom(subProperty, supProperty));
            } else if (tmpAxiom instanceof RI3Axiom){
                RI3Axiom tmpAx = (RI3Axiom) tmpAxiom;
                OWLObjectProperty leftSubProperty = dataFactory.getOWLObjectProperty(IRI.create(prefix+tmpAx.getLeftSubProperty()));
                OWLObjectProperty rightSubProprty = dataFactory.getOWLObjectProperty(IRI.create(prefix+tmpAx.getRightSubProperty()));
                ArrayList<OWLObjectProperty> subPropertyChain = new ArrayList<OWLObjectProperty>();
                subPropertyChain.add(leftSubProperty);
                subPropertyChain.add(rightSubProprty);

                OWLObjectProperty supProperty = dataFactory.getOWLObjectProperty(IRI.create(prefix+tmpAx.getSuperProperty()));

                axioms.add(dataFactory.getOWLSubPropertyChainOfAxiom(subPropertyChain, supProperty));
            }



        }

        manager.addAxioms(ontology, axioms);
        JcelReasoner reasoner = new JcelReasoner(ontology, false);
        RuleBasedReasoner ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();
        TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();

        Map<OWLClass, Integer> classIntegerMap = translatorReposity.getClassInvMap();
        OWLClass classX = dataFactory.getOWLClass(IRI.create(prefix + "1"));
        OWLClass classY = dataFactory.getOWLClass(IRI.create(prefix + "2"));

        Integer intX = classIntegerMap.get(classX);
        Integer intY = classIntegerMap.get(classY);


        IntegerClass intClassX = axiomFat.createClass(intX);
        IntegerClass intClassY = axiomFat.createClass(intY);

        ComplexIntegerAxiom complexIntegerAxiom = cpFat.createSubClassOfAxiom(intClassX, intClassY);


        return ruleBasedReasoner.isEntailed(complexIntegerAxiom);

    }


}

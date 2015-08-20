package utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.DataRangeType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataComplementOf;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataOneOf;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class OWL2Rule {

	private static OWLDataFactory factory;
	private static int functionCount;
    private static int newAtomicCount;
    private static ArrayList<OWLSubClassOfAxiom> axiomList;
    private static ArrayList<OWLAxiom> originList;
    private static OWLAxiom originAxiom;
    private static boolean adoptUNA;
    private static boolean axiomatizeEQ;

    public static final String NEW_ATOMIC_IRI = "http://localhost/newatomic#";
    public static final int NOT_EQUAL_PID = 1;
    public static final int EQUAL_PID = 2;
    public static final IRI NOT_EQUAL_IRI = IRI.create("http://localhost/builtin#neq");
    public static final IRI EQUAL_IRI = IRI.create("http://localhost/builtin#eq");
    public static final IRI UNIFORM_EQ_IRI = IRI.create("http://localhost/builtin#ueq");

    public static List<LogicalRule> translate(OWLOntology ontology, boolean adoptUNA, boolean axiomatizeEQ) {
    	List<LogicalRule> rules = new ArrayList<LogicalRule>();
    	if (translateKernel(ontology, rules, adoptUNA, axiomatizeEQ) && axiomatizeEQ)
			axiomatizeEquality(ontology, rules);
    	return rules;
    }

    public static boolean translateKernel(OWLOntology ontology, List<LogicalRule> rules,
    		boolean adoptUNA, boolean axiomatizeEQ) {
    	return translateKernel(ontology.getAxioms(), rules, adoptUNA, axiomatizeEQ);
    }

    public static boolean translateKernel(Collection<OWLAxiom> axioms, List<LogicalRule> rules,
    		boolean adoptUNA, boolean axiomatizeEQ) {
		OWL2Rule.adoptUNA = adoptUNA;
		OWL2Rule.axiomatizeEQ = axiomatizeEQ;
		factory = OWLDataFactoryImpl.getInstance();
		functionCount = 0;
		newAtomicCount = 0;
		axiomList = new ArrayList<OWLSubClassOfAxiom>();
		originList = new ArrayList<OWLAxiom>();		
		boolean hasEquality = false;

		for (OWLAxiom ax: axioms)
		if (ax instanceof OWLAsymmetricObjectPropertyAxiom) {
			OWLAsymmetricObjectPropertyAxiom axiom = (OWLAsymmetricObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLDataPropertyDomainAxiom) {
			originAxiom = ax;
			OWLDataPropertyDomainAxiom axiom = (OWLDataPropertyDomainAxiom)ax;
			OWLClassExpression domain = axiom.getDomain();
			if (!domain.isOWLThing())
			if (domain.isClassExpressionLiteral()) {
				LogicalRule rule = new LogicalRule();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				arguments[1] = "?Y";
				rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
				arguments = new String[1];
				arguments[0] = "?X";
				if (domain.isAnonymous())
					rule.body.add(new Literal(domain.getComplementNNF().asOWLClass().getIRI(), arguments));
				else
					rule.head.add(new Literal(domain.asOWLClass().getIRI(), arguments));
				rule.origin = axiom;
				rules.add(rule);
			}
			else if (domain.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression c: domain.asConjunctSet())
				if (!c.isOWLThing())
				if (c.isClassExpressionLiteral()) {
					LogicalRule rule = new LogicalRule();
					String[] arguments = new String[2];
					arguments[0] = "?X";
					arguments[1] = "?Y";
					rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
					arguments = new String[1];
					arguments[0] = "?X";
					if (c.isAnonymous())
						rule.body.add(new Literal(c.getComplementNNF().asOWLClass().getIRI(), arguments));
					else
						rule.head.add(new Literal(c.asOWLClass().getIRI(), arguments));
					rule.origin = axiom;
					rules.add(rule);
				}
				else {
					newAtomicCount++;
	                OWLClass newc = factory.getOWLClass(
	                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount))); 
	                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, c));
	                LogicalRule rule = new LogicalRule();
	    			String[] arguments = new String[2];
	    			arguments[0] = "?X";
	    			arguments[1] = "?Y";
	    			rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
	    			arguments = new String[1];
	    			arguments[0] = "?X";
	    			rule.head.add(new Literal(newc.getIRI(), arguments));
	    			rule.origin = axiom;
	                rules.add(rule);
				}
			}
			else if (domain.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
				LogicalRule rule = new LogicalRule();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				arguments[1] = "?Y";
				rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
				for (OWLClassExpression c: domain.asDisjunctSet())
				if (!c.isOWLNothing())
				if (c.isClassExpressionLiteral()) {
					arguments = new String[1];
					arguments[0] = "?X";
					if (c.isAnonymous())
						rule.body.add(new Literal(c.getComplementNNF().asOWLClass().getIRI(), arguments));
					else
						rule.head.add(new Literal(c.asOWLClass().getIRI(), arguments));
				}
				else {
					newAtomicCount++;
	                OWLClass newc = factory.getOWLClass(
	                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount))); 
	                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, c));
	    			arguments = new String[1];
	    			arguments[0] = "?X";
	    			rule.head.add(new Literal(newc.getIRI(), arguments));
				}
				rule.origin = axiom;
				rules.add(rule);
			}
			else {
				newAtomicCount++;
                OWLClass newc = factory.getOWLClass(
                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount))); 
                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, domain));
                LogicalRule rule = new LogicalRule();
    			String[] arguments = new String[2];
    			arguments[0] = "?X";
    			arguments[1] = "?Y";
    			rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
    			arguments = new String[1];
    			arguments[0] = "?X";
    			rule.head.add(new Literal(newc.getIRI(), arguments));
    			rule.origin = axiom;
                rules.add(rule);
			}
		}

		else if (ax instanceof OWLDisjointClassesAxiom) {
			originAxiom = ax;
			OWLDisjointClassesAxiom axiom = (OWLDisjointClassesAxiom)ax;
			List<OWLClassExpression> dcs = axiom.getClassExpressionsAsList();
			for (int i = 1; i < dcs.size(); i++)
			for (int j = 0; j < i; j++)
				handleDisjointPairs(dcs.get(j), dcs.get(i));
		}

		else if (ax instanceof OWLDisjointDataPropertiesAxiom) {
			OWLDisjointDataPropertiesAxiom axiom = (OWLDisjointDataPropertiesAxiom)ax;
			List<OWLDataPropertyExpression> dps = new ArrayList<OWLDataPropertyExpression>(axiom.getProperties());
			for (int i = 1; i < dps.size(); i++)
			for (int j = 0; j < i; j++) {
				LogicalRule rule = new LogicalRule();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				arguments[1] = "?Y";
				rule.body.add(new Literal(dps.get(j).asOWLDataProperty().getIRI(), arguments));
				rule.body.add(new Literal(dps.get(i).asOWLDataProperty().getIRI(), arguments.clone()));
				rule.origin = axiom;
				rules.add(rule);
			}
		}

		else if (ax instanceof OWLDisjointObjectPropertiesAxiom) {
			OWLDisjointObjectPropertiesAxiom axiom = (OWLDisjointObjectPropertiesAxiom)ax;
			List<OWLObjectPropertyExpression> dps = new ArrayList<OWLObjectPropertyExpression>(axiom.getProperties());
			for (int i = 1; i < dps.size(); i++)
			for (int j = 0; j < i; j++) {
				LogicalRule rule = new LogicalRule();
				if (dps.get(j).isAnonymous())
					rule.body.add(new Literal(dps.get(j).getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(dps.get(j).getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				if (dps.get(i).isAnonymous())
					rule.body.add(new Literal(dps.get(i).getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(dps.get(i).getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				rule.origin = axiom;
				rules.add(rule);
			}
		}

		else if (ax instanceof OWLDisjointUnionAxiom) {
			originAxiom = ax;
			OWLDisjointUnionAxiom axiom = (OWLDisjointUnionAxiom)ax;
			List<OWLClassExpression> dcs = new ArrayList<OWLClassExpression>(axiom.getClassExpressions());
			for (int i = 1; i < dcs.size(); i++)
			for (int j = 0; j < i; j++)
				handleDisjointPairs(dcs.get(j), dcs.get(i));
			handleSubClassOf(factory.getOWLSubClassOfAxiom(
					axiom.getOWLClass(), factory.getOWLObjectUnionOf(axiom.getClassExpressions()))); 
			for (OWLClassExpression c: axiom.getClassExpressions())
				handleSubClassOf(factory.getOWLSubClassOfAxiom(c, axiom.getOWLClass()));
		}

		else if (ax instanceof OWLEquivalentClassesAxiom) {
			originAxiom = ax;
			OWLEquivalentClassesAxiom axiom = (OWLEquivalentClassesAxiom)ax;
			List<OWLClassExpression> ecs = axiom.getClassExpressionsAsList();
			for (int i = 0; i < ecs.size(); i++)
				handleSubClassOf(factory.getOWLSubClassOfAxiom((i>0)? ecs.get(i-1): ecs.get(ecs.size()-1), ecs.get(i)));
		}

		else if (ax instanceof OWLEquivalentDataPropertiesAxiom) {
			OWLEquivalentDataPropertiesAxiom axiom = (OWLEquivalentDataPropertiesAxiom)ax;
			List<OWLDataPropertyExpression> eps = new ArrayList<OWLDataPropertyExpression>(axiom.getProperties());
			for (int i = 0; i < eps.size(); i++) {
				LogicalRule rule = new LogicalRule();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				arguments[1] = "?Y";
				OWLDataPropertyExpression subp = (i > 0)? eps.get(i-1): eps.get(eps.size()-1); 
				rule.body.add(new Literal(subp.asOWLDataProperty().getIRI(), arguments));
				rule.head.add(new Literal(eps.get(i).asOWLDataProperty().getIRI(), arguments.clone()));
				rule.origin = axiom;
				rules.add(rule);
			}
		}

		else if (ax instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom axiom = (OWLEquivalentObjectPropertiesAxiom)ax;
			List<OWLObjectPropertyExpression> eps = new ArrayList<OWLObjectPropertyExpression>(axiom.getProperties());
			for (int i = 0; i < eps.size(); i++) {
				LogicalRule rule = new LogicalRule();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				arguments[1] = "?Y";
				OWLObjectPropertyExpression subp = (i > 0)? eps.get(i-1): eps.get(eps.size()-1);
				if (subp.isAnonymous())
					rule.body.add(new Literal(subp.getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(subp.getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				if (eps.get(i).isAnonymous())
					rule.head.add(new Literal(eps.get(i).getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.head.add(new Literal(eps.get(i).getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				rule.origin = axiom;
				rules.add(rule);
			}
		}

		else if (ax instanceof OWLFunctionalDataPropertyAxiom) {
			OWLFunctionalDataPropertyAxiom axiom = (OWLFunctionalDataPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			String[] arguments = new String[2];
			arguments[0] = "?X";
			arguments[1] = "?Y1";
			rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
			arguments = new String[2];
			arguments[0] = "?X";
			arguments[1] = "?Y2";
			rule.body.add(new Literal(axiom.getProperty().asOWLDataProperty().getIRI(), arguments));
			arguments = new String[2];
			arguments[0] = "?Y1";
			arguments[1] = "?Y2";
			rule.body.add(new Literal(NOT_EQUAL_IRI, arguments));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLFunctionalObjectPropertyAxiom) {
			OWLFunctionalObjectPropertyAxiom axiom = (OWLFunctionalObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			if (axiom.getProperty().isAnonymous()) {
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y1", "?X"}));
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y2", "?X"}));
			}
			else {
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y1"}));
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y2"}));
			}
			if (adoptUNA)
				rule.body.add(new Literal(NOT_EQUAL_IRI, new String[]{"?Y1", "?Y2"}));
			else if (axiomatizeEQ) {
				rule.head.add(new Literal(UNIFORM_EQ_IRI, new String[]{"?Y1", "?Y2"}));
				rule.body.add(0, new Literal(NOT_EQUAL_IRI, new String[]{"?Y1", "?Y2"}));
				hasEquality = true;
			}
			else {
				rule.head.add(new Literal(EQUAL_IRI, new String[]{"?Y1", "?Y2"}));
				rule.body.add(new Literal(NOT_EQUAL_IRI, new String[]{"?Y1", "?Y2"}));
				hasEquality = true;
			}
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLInverseFunctionalObjectPropertyAxiom) {
			OWLInverseFunctionalObjectPropertyAxiom axiom = (OWLInverseFunctionalObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			if (axiom.getProperty().isAnonymous()) {
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X1"}));
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X2"}));
			}
			else {
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X1", "?Y"}));
				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X2", "?Y"}));
			}
			if (adoptUNA)
				rule.body.add(new Literal(NOT_EQUAL_IRI, new String[]{"?X1", "?X2"}));
			else if (axiomatizeEQ) {
				rule.head.add(new Literal(UNIFORM_EQ_IRI, new String[]{"?X1", "?X2"}));
				rule.body.add(0, new Literal(NOT_EQUAL_IRI, new String[]{"?X1", "?X2"}));
				hasEquality = true;
			}
			else {
				rule.head.add(new Literal(EQUAL_IRI, new String[]{"?X1", "?X2"}));
				rule.body.add(new Literal(NOT_EQUAL_IRI, new String[]{"?X1", "?X2"}));
				hasEquality = true;
			}
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLInverseObjectPropertiesAxiom) {
			OWLInverseObjectPropertiesAxiom axiom = (OWLInverseObjectPropertiesAxiom)ax;
			LogicalRule rule = new LogicalRule();
			if (axiom.getFirstProperty().isAnonymous())
				rule.body.add(new Literal(axiom.getFirstProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			else
				rule.body.add(new Literal(axiom.getFirstProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			if (axiom.getSecondProperty().isAnonymous())
				rule.head.add(new Literal(axiom.getSecondProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			else
				rule.head.add(new Literal(axiom.getSecondProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			rule.origin = axiom;
			rules.add(rule);
			rule = new LogicalRule();
			if (axiom.getSecondProperty().isAnonymous())
				rule.body.add(new Literal(axiom.getSecondProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			else
				rule.body.add(new Literal(axiom.getSecondProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			if (axiom.getFirstProperty().isAnonymous())
				rule.head.add(new Literal(axiom.getFirstProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			else
				rule.head.add(new Literal(axiom.getFirstProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLIrreflexiveObjectPropertyAxiom) {
			OWLIrreflexiveObjectPropertyAxiom axiom = (OWLIrreflexiveObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?X"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLObjectPropertyDomainAxiom) {
			originAxiom = ax;
			OWLObjectPropertyDomainAxiom axiom = (OWLObjectPropertyDomainAxiom)ax;
			OWLClassExpression domain = axiom.getDomain();
			if (!domain.isOWLThing())
			if (domain.isClassExpressionLiteral()) {
				LogicalRule rule = new LogicalRule();
				if (axiom.getProperty().isAnonymous())
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				if (domain.isAnonymous())
					rule.body.add(new Literal(domain.getComplementNNF().asOWLClass().getIRI(), new String[]{"?X"}));
				else
					rule.head.add(new Literal(domain.asOWLClass().getIRI(), new String[]{"?X"}));
				rule.origin = axiom;
				rules.add(rule);
			}
			else if (domain.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression c: domain.asConjunctSet())
				if (!c.isOWLThing())
				if (c.isClassExpressionLiteral()) {
					LogicalRule rule = new LogicalRule();
					if (axiom.getProperty().isAnonymous())
						rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
					else
						rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
					if (c.isAnonymous())
						rule.body.add(new Literal(c.getComplementNNF().asOWLClass().getIRI(), new String[]{"?X"}));
					else
						rule.head.add(new Literal(c.asOWLClass().getIRI(), new String[]{"?X"}));
					rule.origin = axiom;
					rules.add(rule);
				}
				else {
					newAtomicCount++;
	                OWLClass newc = factory.getOWLClass(
	                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
	                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, c));
	                LogicalRule rule = new LogicalRule();
	    			if (axiom.getProperty().isAnonymous())
	    				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
	    			else
	    				rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
	    			rule.head.add(new Literal(newc.getIRI(), new String[]{"?X"}));
	    			rule.origin = axiom;
	                rules.add(rule);
				}
			}
			else if (domain.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
				LogicalRule rule = new LogicalRule();
				if (axiom.getProperty().isAnonymous())
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				for (OWLClassExpression c: domain.asDisjunctSet())
				if (!c.isOWLNothing())
				if (c.isClassExpressionLiteral()) {
					if (c.isAnonymous())
						rule.body.add(new Literal(c.getComplementNNF().asOWLClass().getIRI(), new String[]{"?X"}));
					else
						rule.head.add(new Literal(c.asOWLClass().getIRI(), new String[]{"?X"}));
				}
				else {
					newAtomicCount++;
	                OWLClass newc = factory.getOWLClass(
	                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
	                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, c));
	    			rule.head.add(new Literal(newc.getIRI(), new String[]{"?X"}));
				}
				rule.origin = axiom;
				rules.add(rule);
			}
			else {
				newAtomicCount++;
	            OWLClass newc = factory.getOWLClass(
	            		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
	            handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, domain));
	            LogicalRule rule = new LogicalRule();
	            if (axiom.getProperty().isAnonymous())
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				rule.head.add(new Literal(newc.getIRI(), new String[]{"?X"}));
				rule.origin = axiom;
	            rules.add(rule);
			}
		}

		else if (ax instanceof OWLObjectPropertyRangeAxiom) {
			originAxiom = ax;
			OWLObjectPropertyRangeAxiom axiom = (OWLObjectPropertyRangeAxiom)ax;
			OWLClassExpression range = axiom.getRange();
			if (!range.isOWLThing())
			if (range.isClassExpressionLiteral()) {
				LogicalRule rule = new LogicalRule();
				if (axiom.getProperty().isAnonymous())
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				if (range.isAnonymous())
					rule.body.add(new Literal(range.getComplementNNF().asOWLClass().getIRI(), new String[]{"?Y"}));
				else
					rule.head.add(new Literal(range.asOWLClass().getIRI(), new String[]{"?Y"}));
				rule.origin = axiom;
				rules.add(rule);
			}
			else if (range.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression c: range.asConjunctSet())
				if (!c.isOWLThing())
				if (c.isClassExpressionLiteral()) {
					LogicalRule rule = new LogicalRule();
					if (axiom.getProperty().isAnonymous())
						rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
					else
						rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
					if (c.isAnonymous())
						rule.body.add(new Literal(c.getComplementNNF().asOWLClass().getIRI(), new String[]{"?X"}));
					else
						rule.head.add(new Literal(c.asOWLClass().getIRI(), new String[]{"?X"}));
					rule.origin = axiom;
					rules.add(rule);
				}
				else {
					newAtomicCount++;
	                OWLClass newc = factory.getOWLClass(
	                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
	                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, c));
	                LogicalRule rule = new LogicalRule();
	    			if (axiom.getProperty().isAnonymous())
						rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
					else
						rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
	    			rule.head.add(new Literal(newc.getIRI(), new String[]{"?X"}));
	    			rule.origin = axiom;
	                rules.add(rule);
				}
			}
			else if (range.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
				LogicalRule rule = new LogicalRule();
				if (axiom.getProperty().isAnonymous())
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				for (OWLClassExpression c: range.asDisjunctSet())
				if (!c.isOWLNothing())
				if (c.isClassExpressionLiteral()) {
					if (c.isAnonymous())
						rule.body.add(new Literal(c.getComplementNNF().asOWLClass().getIRI(), new String[]{"?X"}));
					else
						rule.head.add(new Literal(c.asOWLClass().getIRI(), new String[]{"?X"}));
				}
				else {
					newAtomicCount++;
	                OWLClass newc = factory.getOWLClass(
	                		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
	                handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, c));
	    			rule.head.add(new Literal(newc.getIRI(), new String[]{"?X"}));
				}
				rule.origin = axiom;
				rules.add(rule);
			}
			else {
				newAtomicCount++;
		        OWLClass newc = factory.getOWLClass(
		        		IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
		        handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, range));
		        LogicalRule rule = new LogicalRule();
		        if (axiom.getProperty().isAnonymous())
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				rule.head.add(new Literal(newc.getIRI(), new String[]{"?X"}));
				rule.origin = axiom;
	            rules.add(rule);
			}
		}

		else if (ax instanceof OWLReflexiveObjectPropertyAxiom) {
			OWLReflexiveObjectPropertyAxiom axiom = (OWLReflexiveObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			rule.head.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?X"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLSubDataPropertyOfAxiom) {
			OWLSubDataPropertyOfAxiom axiom = (OWLSubDataPropertyOfAxiom)ax;
			LogicalRule rule = new LogicalRule();
			String[] arguments = new String[2];
			arguments[0] = "?X";
			arguments[1] = "?Y";
			rule.body.add(new Literal(axiom.getSubProperty().asOWLDataProperty().getIRI(), arguments));
			rule.head.add(new Literal(axiom.getSuperProperty().asOWLDataProperty().getIRI(), arguments.clone()));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom axiom = (OWLSubObjectPropertyOfAxiom)ax;
			LogicalRule rule = new LogicalRule();
			if (axiom.getSubProperty().isAnonymous())
				rule.body.add(new Literal(axiom.getSubProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			else
				rule.body.add(new Literal(axiom.getSubProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			if (axiom.getSuperProperty().isAnonymous())
				rule.head.add(new Literal(axiom.getSuperProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			else
				rule.head.add(new Literal(axiom.getSuperProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLSubPropertyChainOfAxiom) {
			OWLSubPropertyChainOfAxiom axiom = (OWLSubPropertyChainOfAxiom)ax;
			LogicalRule rule = new LogicalRule();
			List<OWLObjectPropertyExpression> dps = axiom.getPropertyChain();
			for (int i = 0; i < dps.size(); i++) {
				String arg1 = String.format("?X%d", i+1);
				String arg2 = String.format("?X%d", i+2);
				if (dps.get(i).isAnonymous())
					rule.body.add(new Literal(dps.get(i).getNamedProperty().getIRI(), new String[]{arg2, arg1}));
				else
					rule.body.add(new Literal(dps.get(i).getNamedProperty().getIRI(), new String[]{arg1, arg2}));
			}
			String arg1 = "?X1";
			String arg2 = String.format("?X%d", dps.size()+1);
			if (axiom.getSuperProperty().isAnonymous())
				rule.head.add(new Literal(axiom.getSuperProperty().getNamedProperty().getIRI(), new String[]{arg2, arg1}));
			else
				rule.head.add(new Literal(axiom.getSuperProperty().getNamedProperty().getIRI(), new String[]{arg1, arg2}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLSubClassOfAxiom) {
			originAxiom = ax;
			handleSubClassOf((OWLSubClassOfAxiom)ax);
		}

		else if (ax instanceof OWLSymmetricObjectPropertyAxiom) {
			OWLSymmetricObjectPropertyAxiom axiom = (OWLSymmetricObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			rule.head.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		else if (ax instanceof OWLTransitiveObjectPropertyAxiom) {
			OWLTransitiveObjectPropertyAxiom axiom = (OWLTransitiveObjectPropertyAxiom)ax;
			LogicalRule rule = new LogicalRule();
			rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			rule.body.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?Y", "?Z"}));
			rule.head.add(new Literal(axiom.getProperty().getNamedProperty().getIRI(), new String[]{"?X", "?Z"}));
			rule.origin = axiom;
			rules.add(rule);
		}

		if (translateAxiomList(rules))
			hasEquality = true;

		return hasEquality;
	}

	public static void axiomatizeEquality(OWLOntology ontology, List<LogicalRule> rules) {
		factory = OWLDataFactoryImpl.getInstance();
		// Add the reflexive rule
    	LogicalRule newRule = new LogicalRule();
    	String[] args = new String[] {"?X", "?Y"};
    	newRule.head.add(new Literal(UNIFORM_EQ_IRI, args));
    	newRule.body.add(new Literal(UNIFORM_EQ_IRI, args));
    	rules.add(newRule);
    	// Add the symmetry rule
    	newRule = new LogicalRule();
    	newRule.head.add(new Literal(UNIFORM_EQ_IRI, args));
    	newRule.body.add(new Literal(NOT_EQUAL_IRI, args));
    	newRule.body.add(new Literal(UNIFORM_EQ_IRI, new String[] {"?Y", "?X"}));
    	rules.add(newRule);
    	// Add the transitive rule
    	newRule = new LogicalRule();
    	newRule.head.add(new Literal(UNIFORM_EQ_IRI, args));
    	newRule.body.add(new Literal(NOT_EQUAL_IRI, args));
    	newRule.body.add(new Literal(UNIFORM_EQ_IRI, new String[] {"?X", "?Z"}));
    	newRule.body.add(new Literal(UNIFORM_EQ_IRI, new String[] {"?Z", "?Y"}));
    	rules.add(newRule);
    	// Add the replacement rules
    	for (OWLClass c: ontology.getClassesInSignature())
    	if (!c.equals(factory.getOWLThing()) && !c.equals(factory.getOWLNothing())) {
    		newRule = new LogicalRule();
    		newRule.head.add(new Literal(c.getIRI(), new String[] {"?X"}));
    		newRule.body.add(new Literal(UNIFORM_EQ_IRI, args));
    		newRule.body.add(new Literal(c.getIRI(), new String[] {"?Y"}));
    		rules.add(newRule);
    	}
    	for (OWLObjectProperty p: ontology.getObjectPropertiesInSignature())
    	if (!p.equals(factory.getOWLTopObjectProperty()) && !p.equals(factory.getOWLBottomObjectProperty())) {
    		newRule = new LogicalRule();
    		newRule.head.add(new Literal(p.getIRI(), new String[] {"?X", "?Z"}));
    		newRule.body.add(new Literal(UNIFORM_EQ_IRI, args));
    		newRule.body.add(new Literal(p.getIRI(), new String[] {"?Y", "?Z"}));
    		rules.add(newRule);
    		newRule = new LogicalRule();
    		newRule.head.add(new Literal(p.getIRI(), new String[] {"?Z", "?X"}));
    		newRule.body.add(new Literal(UNIFORM_EQ_IRI, args));
    		newRule.body.add(new Literal(p.getIRI(), new String[] {"?Z", "?Y"}));
    		rules.add(newRule);
    	}
    	for (OWLDataProperty p: ontology.getDataPropertiesInSignature())
    	if (!p.equals(factory.getOWLTopDataProperty()) && !p.equals(factory.getOWLBottomDataProperty())) {
    		newRule = new LogicalRule();
    		newRule.head.add(new Literal(p.getIRI(), new String[] {"?X", "?Z"}));
    		newRule.body.add(new Literal(UNIFORM_EQ_IRI, args));
    		newRule.body.add(new Literal(p.getIRI(), new String[] {"?Y", "?Z"}));
    		rules.add(newRule);
    	}
	}

	public static LogicalRule parseSentence(String line, String base) {
		LogicalRule rule = new LogicalRule();
		List<Literal> atoms = rule.head;
		int st = 0;
		while (st >= 0) {
			while (st < line.length() && line.charAt(st) <= ' ')
				st++;
			if (st < line.length()-1 && line.charAt(st) == 'v' && line.charAt(st+1) == ' ') {
				st += 2;
				Literal lit = new Literal();
				st = parseLiteral(lit, line, st, base);
				if (st >= 0) {
					atoms.add(lit);
					if (st >= line.length() || line.charAt(st) == '.')
						break;
					if (line.charAt(st) != ':')
						st++;
				}
			}
			else if (st < line.length()-1 && line.charAt(st) == ':' && line.charAt(st+1) == '-') {
				st += 2;
				atoms = rule.body;
			}
			else {
				Literal lit = new Literal();
				st = parseLiteral(lit, line, st, base);
				if (st >= 0) {
					atoms.add(lit);
					if (st >= line.length() || line.charAt(st) == '.')
						break;
					if (line.charAt(st) != ':')
						st++;
				}
			}
		}
		return rule;
	}

	private static int parseLiteral(Literal lit, String line, int st, String base) {
		// read the predicate name
		while (st < line.length() && line.charAt(st) <= ' ')
			st++;
		int ed = st;
		while (ed < line.length() && line.charAt(ed) != '(')
			ed++;
		if (ed == st)
			return -1;
		String predName = line.substring(st, ed);
		if (predName.equalsIgnoreCase("EQ"))
			lit.predicate = EQUAL_IRI;
		else if (predName.equalsIgnoreCase("NEQ"))
			lit.predicate = NOT_EQUAL_IRI;
		else if (predName.indexOf('#') < 0)
			lit.predicate = IRI.create(base + predName);
		else
			lit.predicate = IRI.create(predName);
		// read the first argument
		st = ed+1;
		while (st < line.length() && line.charAt(st) <= ' ')
			st++;
		int indent = 0;
		ed = st;
		while (ed < line.length()) {
			if (indent == 0 && (line.charAt(ed) == ',' || line.charAt(ed) == ')'))
				break;
			if (line.charAt(ed) == '(')
				indent++;
			else if (line.charAt(ed) == ')')
				indent--;
			ed++;
		}
		if (ed == st || ed == line.length())
			return -1;
		String arg1 = line.substring(st, ed);
		// read the second argument
		if (line.charAt(ed) == ',') {
			st = ed+1; 
			while (st < line.length() && line.charAt(st) <= ' ')
				st++;
			indent = 0;
			ed = st;
			while (ed < line.length()) {
				if (indent == 0 && line.charAt(ed) == ')')
					break;
				if (line.charAt(ed) == '(')
					indent++;
				else if (line.charAt(ed) == ')')
					indent--;
				ed++;
			}
			if (ed == st || ed == line.length())
				return -1;
			lit.arguments = new String[2];
			lit.arguments[0] = arg1;
			lit.arguments[1] = line.substring(st, ed);
		}
		else {
			lit.arguments = new String[1];
			lit.arguments[0] = arg1;
		}
		return ed+1;
	}

	private static boolean translateAxiomList(List<LogicalRule> rules) {
		boolean hasEquality = false;

		for (int k = 0; k < axiomList.size(); k++) {
			OWLClassExpression subDesc = axiomList.get(k).getSubClass();
			OWLClassExpression supDesc = axiomList.get(k).getSuperClass();

			LogicalRule rule = null;
			if (subDesc.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				rule = new LogicalRule();
				for (OWLClassExpression c: subDesc.asConjunctSet())
					if (translateDescription(c, rule))
						hasEquality = true;
			}
			else if (subDesc.getClassExpressionType() == ClassExpressionType.OBJECT_ONE_OF) {
				for (OWLIndividual value: ((OWLObjectOneOf)subDesc).getIndividuals()) {
					rule = new LogicalRule();
					String[] arguments = new String[1];
					arguments[0] = value.asOWLNamedIndividual().getIRI().toString();
					rule.head.add(new Literal(supDesc.asOWLClass().getIRI(), arguments));
					rule.origin = originList.get(k);
					rules.add(rule);
				}
				supDesc = null;
			}
			else {
				rule = new LogicalRule();
				if (!subDesc.isOWLThing())
					if (translateDescription(subDesc, rule))
						hasEquality = true;
			}

			if (supDesc != null)
			if (supDesc.getClassExpressionType() == ClassExpressionType.DATA_HAS_VALUE) {
				OWLDataPropertyExpression pred = ((OWLDataHasValue)supDesc).getProperty();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				if (((OWLDataHasValue)supDesc).getValue().isDouble())
					arguments[1] = String.format("%.2f", ((OWLDataHasValue)supDesc).getValue().parseDouble());
				else if (((OWLDataHasValue)supDesc).getValue().isFloat())
					arguments[1] = String.format("%.2f", ((OWLDataHasValue)supDesc).getValue().parseFloat());
				else if (((OWLDataHasValue)supDesc).getValue().isInteger())
					arguments[1] = String.format("%d", ((OWLDataHasValue)supDesc).getValue().parseInteger());
				else
					arguments[1] = String.format("\"%s\"", ((OWLDataHasValue)supDesc).getValue().getLiteral());
				rule.head.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
				rule.origin = originList.get(k);
				rules.add(rule);
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.DATA_MIN_CARDINALITY) {
				int minc = ((OWLDataMinCardinality)supDesc).getCardinality();
				OWLDataPropertyExpression pred = ((OWLDataMinCardinality)supDesc).getProperty();
				int start = functionCount;
				for (int i = 1; i <= minc; i++) {
					LogicalRule rule1 = new LogicalRule();
					rule1.body.addAll(rule.body);
					rule1.head.addAll(rule.head);
					String[] arguments = new String[2];
					arguments[0] = "?X";
					arguments[1] = String.format("?f%d(X)", functionCount++);
					rule1.head.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
					rule1.origin = originList.get(k);
					rules.add(rule1);
				}
				for (int i = 0; i < minc; i++)
				for (int j = i+1; j < minc; j++) {
					LogicalRule rule1 = new LogicalRule();
					String[] arguments = new String[2];
					arguments[0] = String.format("?f%d(X)", i+start);
					arguments[1] = String.format("?f%d(X)", j+start);
					rule1.head.add(new Literal(NOT_EQUAL_IRI, arguments));
					rule1.origin = originList.get(k);
					rules.add(rule1);
				}
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.DATA_SOME_VALUES_FROM) {
				OWLDataPropertyExpression pred = ((OWLDataSomeValuesFrom)supDesc).getProperty();
				String[] arguments = new String[2];
				arguments[0] = "?X";
				if (((OWLDataSomeValuesFrom)supDesc).getFiller() instanceof OWLDataOneOf) {
					OWLDataOneOf oneOf = (OWLDataOneOf)((OWLDataSomeValuesFrom)supDesc).getFiller();
					for (OWLLiteral lit: oneOf.getValues())
					if (lit.isDouble())
						arguments[1] = String.format("%.2f", lit.parseDouble());
					else if (lit.isFloat())
						arguments[1] = String.format("%.2f", lit.parseFloat());
					else if (lit.isInteger())
						arguments[1] = String.format("%d", lit.parseInteger());
					else
						arguments[1] = String.format("\"%s\"", lit.getLiteral());
				}
				else
					arguments[1] = String.format("?f%d(X)", functionCount++);
				rule.head.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
				rule.origin = originList.get(k);
				rules.add(rule);
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OBJECT_HAS_SELF) {
				OWLObjectPropertyExpression pred = ((OWLObjectHasSelf)supDesc).getProperty();
				rule.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{"?X", "?X"}));
				rule.origin = originList.get(k);
				rules.add(rule);
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OBJECT_HAS_VALUE) {
				OWLObjectPropertyExpression pred = ((OWLObjectHasValue)supDesc).getProperty();
				OWLIndividual value = ((OWLObjectHasValue)supDesc).getValue();
				String arg1 = "?X";
				String arg2 = value.asOWLNamedIndividual().getIRI().toString();
				if (pred.isAnonymous())
					rule.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg2, arg1}));
				else
					rule.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg1, arg2}));
				rule.origin = originList.get(k);
				rules.add(rule);
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OBJECT_MIN_CARDINALITY) {
				int minc = ((OWLObjectMinCardinality)supDesc).getCardinality();
				OWLObjectPropertyExpression pred = ((OWLObjectMinCardinality)supDesc).getProperty();
				OWLClassExpression tail = ((OWLObjectMinCardinality)supDesc).getFiller();
				int start = functionCount;
				for (int i = 1; i <= minc; i++) {
					LogicalRule rule1 = new LogicalRule();
					rule1.body.addAll(rule.body);
					rule1.head.addAll(rule.head);
					String arg1 = "?X";
					String arg2 = String.format("?f%d(X)", functionCount++);
					if (pred.isAnonymous())
						rule1.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg2, arg1}));
					else
						rule1.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg1, arg2}));
					rule1.origin = originList.get(k);
					rules.add(rule1);
				}
				if (!tail.isOWLThing())
				if (tail.isAnonymous()) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					OWLClassExpression ntail = ((OWLObjectComplementOf)tail).getOperand();
					LogicalRule rule1 = new LogicalRule();
					String[] arguments = new String[1];
					arguments[0] = "?X";
					rule1.body.add(new Literal(newc.getIRI(), arguments));
					rule1.body.add(new Literal(ntail.asOWLClass().getIRI(), arguments));
					rule1.origin = originList.get(k);
					rules.add(rule1);
					for (int i = 0; i < minc; i++) {
						rule1 = new LogicalRule();
						rule1.body.addAll(rule.body);
						rule1.head.addAll(rule.head);
						arguments = new String[1];
						arguments[0] = String.format("?f%d(X)", i+start);
						rule1.head.add(new Literal(newc.getIRI(), arguments));
						rule1.origin = originList.get(k);
						rules.add(rule1);
					}
				}
				else {
					for (int i = 0; i < minc; i++) {
						LogicalRule rule1 = new LogicalRule();
						rule1.body.addAll(rule.body);
						rule1.head.addAll(rule.head);
						String[] arguments = new String[1];
						arguments[0] = String.format("?f%d(X)", i+start);
						rule1.head.add(new Literal(tail.asOWLClass().getIRI(), arguments));
						rule1.origin = originList.get(k);
						rules.add(rule1);
					}
				}
				for (int i = 0; i < minc; i++)
				for (int j = i+1; j < minc; j++) {
					LogicalRule rule1 = new LogicalRule();
					String[] arguments = new String[2];
					arguments[0] = String.format("?f%d(X)", i+start);
					arguments[1] = String.format("?f%d(X)", j+start);
					if (adoptUNA)
						rule1.head.add(new Literal(NOT_EQUAL_IRI, arguments));
					else if (axiomatizeEQ)
						rule1.body.add(new Literal(UNIFORM_EQ_IRI, arguments));
					else
						rule1.body.add(new Literal(EQUAL_IRI, arguments));
					rule1.origin = originList.get(k);
					rules.add(rule1);
				}
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OBJECT_ONE_OF) {
				for (OWLIndividual value: ((OWLObjectOneOf)supDesc).getIndividuals()) {
					String[] arguments = new String[2];
					arguments[0] = "?X";
					arguments[1] = value.asOWLNamedIndividual().getIRI().toString();
					if (adoptUNA)
						rule.body.add(new Literal(NOT_EQUAL_IRI, arguments));
					else if (axiomatizeEQ) {
						rule.head.add(new Literal(UNIFORM_EQ_IRI, arguments));
						rule.body.add(0, new Literal(NOT_EQUAL_IRI, arguments));
						hasEquality = true;
					}
					else {
						rule.head.add(new Literal(EQUAL_IRI, arguments));
						rule.body.add(new Literal(NOT_EQUAL_IRI, arguments));
						hasEquality = true;
					}
				}
				rule.origin = originList.get(k);
				rules.add(rule);
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM) {
				OWLObjectPropertyExpression pred = ((OWLObjectSomeValuesFrom)supDesc).getProperty();
				OWLClassExpression tail = ((OWLObjectSomeValuesFrom)supDesc).getFiller();
				LogicalRule rule1 = new LogicalRule();
				rule1.body.addAll(rule.body);
				rule1.head.addAll(rule.head);
				String arg1 = "?X";
				String arg2 = String.format("?f%d(X)", functionCount++);
				if (pred.isAnonymous())
					rule1.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg2, arg1}));
				else
					rule1.head.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg1, arg2}));
				rule1.origin = originList.get(k);
				rules.add(rule1);
				if (!tail.isOWLThing())
				if (tail.isAnonymous()) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					OWLClassExpression ntail = ((OWLObjectComplementOf)tail).getOperand();
					rule1 = new LogicalRule();
					rule1.body.add(new Literal(newc.getIRI(), new String[]{"?X"}));
					rule1.body.add(new Literal(ntail.asOWLClass().getIRI(),  new String[]{"?X"}));
					rule1.origin = originList.get(k);
					rules.add(rule1);
					rule1 = new LogicalRule();
					rule1.body.addAll(rule.body);
					rule1.head.addAll(rule.head);
					String arg = String.format("?f%d(X)", functionCount-1);
					rule1.head.add(new Literal(newc.getIRI(),  new String[]{arg}));
					rule1.origin = originList.get(k);
					rules.add(rule1);
				}
				else {
					rule1 = new LogicalRule();
					rule1.body.addAll(rule.body);
					rule1.head.addAll(rule.head);
					String arg = String.format("?f%d(X)", functionCount-1);
					rule1.head.add(new Literal(tail.asOWLClass().getIRI(), new String[]{arg}));
					rule1.origin = originList.get(k);
					rules.add(rule1);
				}
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
				String[] arguments = new String[1];
				arguments[0] = "?X";
				for (OWLClassExpression c: supDesc.asDisjunctSet())
				if (c.getClassExpressionType() == ClassExpressionType.OBJECT_ONE_OF) {
					for (OWLIndividual value: ((OWLObjectOneOf)c).getIndividuals()) {
						String[] arguments1 = new String[2];
						arguments1[0] = "?X";
						arguments1[1] = value.asOWLNamedIndividual().getIRI().toString();
						if (adoptUNA)
							rule.body.add(new Literal(NOT_EQUAL_IRI, arguments1));
						else if (axiomatizeEQ) {
							rule.head.add(new Literal(UNIFORM_EQ_IRI, arguments1));
							rule.body.add(0, new Literal(NOT_EQUAL_IRI, arguments1));
							hasEquality = true;
						}
						else {
							rule.head.add(new Literal(EQUAL_IRI, arguments1));
							rule.body.add(new Literal(NOT_EQUAL_IRI, arguments1));
							hasEquality = true;
						}
					}
				}
				else
					rule.head.add(new Literal(c.asOWLClass().getIRI(), arguments));
				rule.origin = originList.get(k);
				rules.add(rule);
			}
			else if (supDesc.getClassExpressionType() == ClassExpressionType.OWL_CLASS) {
				if (!supDesc.isOWLNothing()) {
					String[] arguments = new String[1];
					arguments[0] = "?X";
					rule.head.add(new Literal(supDesc.asOWLClass().getIRI(), arguments));
				}
				rule.origin = originList.get(k);
				rules.add(rule);
			}
		}

		return hasEquality;
	}

	private static boolean translateDescription(OWLClassExpression c, LogicalRule rule) {
		boolean hasEquality = false;

		if (c.getClassExpressionType() == ClassExpressionType.DATA_HAS_VALUE)  {
			OWLDataPropertyExpression pred = ((OWLDataHasValue)c).getProperty();
			String[] arguments = new String[2];
			arguments[0] = "?X";
			if (((OWLDataHasValue)c).getValue().isDouble())
				arguments[1] = String.format("%.2f", ((OWLDataHasValue)c).getValue().parseDouble());
			else if (((OWLDataHasValue)c).getValue().isFloat())
				arguments[1] = String.format("%.2f", ((OWLDataHasValue)c).getValue().parseFloat());
			else if (((OWLDataHasValue)c).getValue().isInteger())
				arguments[1] = String.format("%d", ((OWLDataHasValue)c).getValue().parseInteger());
			else
				arguments[1] = String.format("\"%s\"", ((OWLDataHasValue)c).getValue().getLiteral());
			rule.body.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
		}

		else if (c.getClassExpressionType() == ClassExpressionType.DATA_MIN_CARDINALITY) {
			int minc = ((OWLDataMinCardinality)c).getCardinality();
			OWLDataPropertyExpression pred = ((OWLDataMinCardinality)c).getProperty();
			if (minc == 1) {
				String[] arguments = new String[2];
				arguments[0] = "?X";
				arguments[1] = "?Y";
				rule.body.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
			}
			else {
				for (int i = 1; i <= minc; i++) {
					String[] arguments = new String[2];
					arguments[0] = "?X";
					arguments[1] = String.format("?Y%d", i);
					rule.body.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
				}
				for (int i = 1; i <= minc; i++)
				for (int j = i+1; j <= minc; j++) {
					String[] arguments = new String[2];
					arguments[0] = String.format("?Y%d", i);
					arguments[1] = String.format("?Y%d", j);
					rule.body.add(new Literal(NOT_EQUAL_IRI, arguments));
				}
			}
		}

		else if (c.getClassExpressionType() == ClassExpressionType.DATA_SOME_VALUES_FROM) {
			OWLDataPropertyExpression pred = ((OWLDataSomeValuesFrom)c).getProperty();
			String[] arguments = new String[2];
			arguments[0] = "?X";
			if (((OWLDataSomeValuesFrom)c).getFiller() instanceof OWLDataOneOf) {
				OWLDataOneOf oneOf = (OWLDataOneOf)((OWLDataSomeValuesFrom)c).getFiller();
				for (OWLLiteral lit: oneOf.getValues())
				if (lit.isDouble())
					arguments[1] = String.format("%.2f", lit.parseDouble());
				else if (lit.isFloat())
					arguments[1] = String.format("%.2f", lit.parseFloat());
				else if (lit.isInteger())
					arguments[1] = String.format("%d", lit.parseInteger());
				else
					arguments[1] = String.format("\"%s\"", lit.getLiteral());
			}
			else
				arguments[1] = "?Y";
			rule.body.add(new Literal(pred.asOWLDataProperty().getIRI(), arguments));
		}

		else if (c.getClassExpressionType() == ClassExpressionType.OBJECT_HAS_SELF) {
			OWLObjectPropertyExpression pred = ((OWLObjectHasSelf)c).getProperty();
			rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{"?X", "?X"}));
		}

		else if (c.getClassExpressionType() == ClassExpressionType.OBJECT_HAS_VALUE) {
			OWLObjectPropertyExpression pred = ((OWLObjectHasValue)c).getProperty();
			OWLIndividual value = ((OWLObjectHasValue)c).getValue();
			String arg1 = "?X";
			String arg2 = value.asOWLNamedIndividual().getIRI().toString();
			if (pred.isAnonymous())
				rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg2, arg1}));
			else
				rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg1, arg2}));
		}

		else if (c.getClassExpressionType() == ClassExpressionType.OBJECT_MIN_CARDINALITY) {
			int minc = ((OWLObjectMinCardinality)c).getCardinality();
			OWLObjectPropertyExpression pred = ((OWLObjectMinCardinality)c).getProperty();
			OWLClassExpression tail = ((OWLObjectMinCardinality)c).getFiller();
			if (minc == 1) {
				if (pred.isAnonymous())
					rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
				else
					rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
				if (!tail.isOWLThing())
				if (tail.isAnonymous()) {
					OWLClassExpression ntail = ((OWLObjectComplementOf)tail).getOperand();
					rule.head.add(new Literal(ntail.asOWLClass().getIRI(), new String[]{"?Y"}));
				}
				else {
					rule.body.add(new Literal(tail.asOWLClass().getIRI(), new String[]{"?Y"}));
				}
			}
			else {
				for (int i = 1; i <= minc; i++) {
					String arg1 = "?X";
					String arg2 = String.format("?Y%d", i);
					if (pred.isAnonymous())
						rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg2, arg1}));
					else
						rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{arg1, arg2}));
				}
				if (!tail.isOWLThing())
				if (tail.isAnonymous()) {
					OWLClassExpression ntail = ((OWLObjectComplementOf)tail).getOperand();
					for (int i = 1; i <= minc; i++) {
						String[] arguments = new String[1];
						arguments[0] = String.format("?Y%d", i);
						rule.head.add(new Literal(ntail.asOWLClass().getIRI(), arguments));
					}
				}
				else {
					for (int i = 1; i <= minc; i++) {
						String[] arguments = new String[1];
						arguments[0] = String.format("?Y%d", i);
						rule.body.add(new Literal(tail.asOWLClass().getIRI(), arguments));
					}
				}
				for (int i = 1; i <= minc; i++)
				for (int j = i+1; j <= minc; j++) {
					String[] arguments = new String[2];
					arguments[0] = String.format("?Y%d", i);
					arguments[1] = String.format("?Y%d", j);
					if (adoptUNA)
						rule.body.add(new Literal(NOT_EQUAL_IRI, arguments));
					else if (axiomatizeEQ) {
						rule.head.add(new Literal(UNIFORM_EQ_IRI, arguments));
						rule.body.add(0, new Literal(NOT_EQUAL_IRI, arguments));
						hasEquality = true;
					}
					else {
						rule.head.add(new Literal(EQUAL_IRI, arguments));
						rule.body.add(new Literal(NOT_EQUAL_IRI, arguments));
						hasEquality = true;
					}
				}
			}
		}

		else if (c.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM) {
			OWLObjectPropertyExpression pred = ((OWLObjectSomeValuesFrom)c).getProperty();
			OWLClassExpression tail = ((OWLObjectSomeValuesFrom)c).getFiller();
			if (pred.isAnonymous())
				rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{"?Y", "?X"}));
			else
				rule.body.add(new Literal(pred.getNamedProperty().getIRI(), new String[]{"?X", "?Y"}));
			if (!tail.isOWLThing())
			if (tail.isAnonymous()) {
				OWLClassExpression ntail = ((OWLObjectComplementOf)tail).getOperand();
				rule.head.add(new Literal(ntail.asOWLClass().getIRI(), new String[]{"?Y"}));
			}
			else {
				rule.body.add(new Literal(tail.asOWLClass().getIRI(), new String[]{"?Y"}));
			}
		}

		else if (c.getClassExpressionType() == ClassExpressionType.OBJECT_ONE_OF) {
			OWLObjectOneOf oneOf = (OWLObjectOneOf)c;
			String[] arguments = new String[2];
			arguments[0] = "?X";
			for (OWLIndividual ind: oneOf.getIndividuals())
				arguments[1] = ind.asOWLNamedIndividual().getIRI().toString();
			if (adoptUNA)
				rule.head.add(new Literal(NOT_EQUAL_IRI, arguments));
			else if (axiomatizeEQ)
				rule.body.add(new Literal(UNIFORM_EQ_IRI, arguments));
			else
				rule.body.add(new Literal(EQUAL_IRI, arguments));
		}

		else if (c.getClassExpressionType() == ClassExpressionType.OWL_CLASS) {
			String[] arguments = new String[1];
			arguments[0] = "?X";
			rule.body.add(new Literal(c.asOWLClass().getIRI(), arguments));
		}

		return hasEquality;
	}

	private static void handleDisjointPairs(OWLClassExpression sub,	OWLClassExpression sup) {
		OWLClassExpression subNNF = sub.getNNF();
		OWLClassExpression superNot = sup.getComplementNNF();
		if (subNNF.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
			for (OWLClassExpression subDesc: subNNF.asDisjunctSet())
			if (superNot.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression superDesc: superNot.asConjunctSet())
					handleSubClassOf(subDesc, superDesc);
			}
			else
				handleSubClassOf(subDesc, superNot);
		}
		else {
			if (superNot.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression superDesc: superNot.asConjunctSet())
					handleSubClassOf(subNNF, superDesc);
			}
			else
				handleSubClassOf(subNNF, superNot);
		}
	}

	private static void handleSubClassOf(OWLSubClassOfAxiom scAxiom) {
		OWLClassExpression subNNF = scAxiom.getSubClass().getNNF();
		OWLClassExpression superNNF = scAxiom.getSuperClass().getNNF();
		if (subNNF.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
			for (OWLClassExpression subDesc: subNNF.asDisjunctSet())
			if (superNNF.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression superDesc: superNNF.asConjunctSet())
					handleSubClassOf(subDesc, superDesc);
			}
			else
				handleSubClassOf(subDesc, superNNF);
		}
		else {
			if (superNNF.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				for (OWLClassExpression superDesc: superNNF.asConjunctSet())
					handleSubClassOf(subNNF, superDesc);
			}
			else
				handleSubClassOf(subNNF, superNNF);
		}
	}

	private static void handleSubClassOf(OWLClassExpression sub, OWLClassExpression sup) {
		if (sup.getClassExpressionType() == ClassExpressionType.DATA_EXACT_CARDINALITY) {
			OWLClassExpression supAnd = ((OWLDataExactCardinality)sup).asIntersectionOfMinMax();
			for (OWLClassExpression supDesc: supAnd.asConjunctSet())
				handleDescription(factory.getOWLObjectUnionOf(sub.getComplementNNF(), supDesc));
		}
		else if (sup.getClassExpressionType() == ClassExpressionType.OBJECT_EXACT_CARDINALITY) {
			OWLClassExpression supAnd = ((OWLObjectExactCardinality)sup).asIntersectionOfMinMax();
			for (OWLClassExpression supDesc: supAnd.asConjunctSet())
				handleDescription(factory.getOWLObjectUnionOf(sub.getComplementNNF(), supDesc));
		}
		else
			handleDescription(factory.getOWLObjectUnionOf(sub.getComplementNNF(), sup));
	}

	private static void handleDescription(OWLObjectUnionOf or) {
		if (or.isOWLThing())
			return;

		ArrayList<OWLClassExpression> subDescs = new ArrayList<OWLClassExpression>();
		ArrayList<OWLClassExpression> supDescs = new ArrayList<OWLClassExpression>();

		for (OWLClassExpression desc: or.asDisjunctSet()) {
			if (desc.getClassExpressionType() == ClassExpressionType.DATA_ALL_VALUES_FROM) {
				OWLDataPropertyExpression pred = ((OWLDataAllValuesFrom)desc).getProperty();
				OWLDataRange range = ((OWLDataAllValuesFrom)desc).getFiller();
				if (range.getDataRangeType() == DataRangeType.DATA_COMPLEMENT_OF)
					range = ((OWLDataComplementOf)range).getDataRange();
				else
					range = factory.getOWLDataComplementOf(range);
				if (hasTwoOrMoreExistence(or)) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					handleSubClassOf(factory.getOWLSubClassOfAxiom(
							factory.getOWLDataSomeValuesFrom(pred, range), newc));
					subDescs.add(newc);
				}
				else
					subDescs.add(factory.getOWLDataSomeValuesFrom(pred, range));
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.DATA_MAX_CARDINALITY) {
				int maxc = ((OWLDataMaxCardinality)desc).getCardinality();
				OWLDataPropertyExpression pred = ((OWLDataMaxCardinality)desc).getProperty();
				OWLDataRange range = ((OWLDataMaxCardinality)desc).getFiller();
				subDescs.add(factory.getOWLDataMinCardinality(maxc+1, pred, range));
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM) {
				OWLObjectPropertyExpression pred = ((OWLObjectAllValuesFrom)desc).getProperty();
				OWLClassExpression tail = ((OWLObjectAllValuesFrom)desc).getFiller();
				if (isNotOneOf(tail)) {
					OWLObjectOneOf oneOf = (OWLObjectOneOf) ((OWLObjectComplementOf)tail).getOperand();
					for (OWLIndividual value: oneOf.getIndividuals())
						subDescs.add(factory.getOWLObjectHasValue(pred, value));
					tail = null;
				}
				else if (!tail.isClassExpressionLiteral()) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					OWLClassExpression negTail = factory.getOWLObjectComplementOf(tail).getNNF();
					if (isPosDescription(negTail)) {
						handleSubClassOf(factory.getOWLSubClassOfAxiom(negTail, newc));
						tail = newc;
					}
					else {
						handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, tail));
						tail = factory.getOWLObjectComplementOf(newc);
					}
				}
				else if (tail.isAnonymous())
					tail = ((OWLObjectComplementOf)tail).getOperand();
				else
					tail = factory.getOWLObjectComplementOf(tail);
				if (tail != null)
				if (hasTwoOrMoreExistence(or)) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					handleSubClassOf(factory.getOWLSubClassOfAxiom(
							factory.getOWLObjectSomeValuesFrom(pred, tail), newc));
					subDescs.add(newc);
				}
				else
					subDescs.add(factory.getOWLObjectSomeValuesFrom(pred, tail));
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF) {
				subDescs.add(((OWLObjectComplementOf)desc).getOperand());
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				newAtomicCount++;
				OWLClass newc = factory.getOWLClass(
						IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
				handleSubClassOf(factory.getOWLSubClassOfAxiom(
						factory.getOWLObjectComplementOf(newc), desc));
				subDescs.add(newc);
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.OBJECT_MAX_CARDINALITY) {
				int maxc = ((OWLObjectMaxCardinality)desc).getCardinality();
				OWLObjectPropertyExpression pred = ((OWLObjectMaxCardinality)desc).getProperty();
				OWLClassExpression tail = ((OWLObjectMaxCardinality)desc).getFiller();
				if (!tail.isClassExpressionLiteral()) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					OWLClassExpression negTail = factory.getOWLObjectComplementOf(tail).getNNF();
					if (isPosDescription(negTail)) {
						handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, negTail));
						tail = newc;
					}
					else {
						handleSubClassOf(factory.getOWLSubClassOfAxiom(tail, newc));
						tail = factory.getOWLObjectComplementOf(newc);
					}
				}
				subDescs.add(factory.getOWLObjectMinCardinality(maxc+1, pred, tail));
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.OBJECT_MIN_CARDINALITY) {
				int minc = ((OWLObjectMinCardinality)desc).getCardinality();
				OWLObjectPropertyExpression pred = ((OWLObjectMinCardinality)desc).getProperty();
				OWLClassExpression tail = ((OWLObjectMinCardinality)desc).getFiller();
				if (!tail.isClassExpressionLiteral()) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					supDescs.add(factory.getOWLObjectMinCardinality(minc, pred, newc));
					if (isNotOneOf(tail)) {
						newAtomicCount++;
						OWLClass newc1 = factory.getOWLClass(
								IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
						handleDescription(factory.getOWLObjectUnionOf(newc, newc1));
						handleSubClassOf(factory.getOWLSubClassOfAxiom(
								((OWLObjectComplementOf)tail).getOperand(), newc1));
					}
					else
						handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, tail));
				}
				else
					supDescs.add(desc);
			}

			else if (desc.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM) {
				OWLObjectPropertyExpression pred = ((OWLObjectSomeValuesFrom)desc).getProperty();
				OWLClassExpression tail = ((OWLObjectSomeValuesFrom)desc).getFiller();
				if (tail.isClassExpressionLiteral())
					supDescs.add(desc);
				else if (tail.getClassExpressionType() == ClassExpressionType.OBJECT_ONE_OF) {
					for (OWLIndividual value: ((OWLObjectOneOf)tail).getIndividuals())
						supDescs.add(factory.getOWLObjectHasValue(pred, value));
				}
				else if (!tail.isClassExpressionLiteral()) {
					newAtomicCount++;
					OWLClass newc = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					supDescs.add(factory.getOWLObjectSomeValuesFrom(pred, newc));
					if (isNotOneOf(tail)) {
						newAtomicCount++;
						OWLClass newc1 = factory.getOWLClass(
								IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
						handleDescription(factory.getOWLObjectUnionOf(newc, newc1));
						handleSubClassOf(factory.getOWLSubClassOfAxiom(
								((OWLObjectComplementOf)tail).getOperand(), newc1));
					}
					else
						handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, tail));
				}
			}

			else
				supDescs.add(desc);
		}

		OWLClassExpression subDesc;
		if (subDescs.size() == 0)
			subDesc = factory.getOWLThing();
		else if (subDescs.size() == 1)
			subDesc = subDescs.get(0);
		else
			subDesc = factory.getOWLObjectIntersectionOf(new HashSet<OWLClassExpression>(subDescs));

		OWLClassExpression supDesc;
		if (supDescs.size() == 0)
			supDesc = factory.getOWLNothing();
		else if (supDescs.size() == 1)
			supDesc = supDescs.get(0);
		else {
			for (int i = 0; i < supDescs.size(); i++)
			if (supDescs.get(i).getClassExpressionType() != ClassExpressionType.OWL_CLASS && 
				supDescs.get(i).getClassExpressionType() != ClassExpressionType.OBJECT_ONE_OF) {
				newAtomicCount++;
				OWLClass newc = factory.getOWLClass(
						IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
				if (isNotOneOf(supDescs.get(i))) {
					newAtomicCount++;
					OWLClass newc1 = factory.getOWLClass(
							IRI.create(String.format("%sQ%d", NEW_ATOMIC_IRI, newAtomicCount)));
					handleDescription(factory.getOWLObjectUnionOf(newc, newc1));
					handleSubClassOf(factory.getOWLSubClassOfAxiom(
							((OWLObjectComplementOf)supDescs.get(i)).getOperand(), newc1));
				}
				else
					handleSubClassOf(factory.getOWLSubClassOfAxiom(newc, supDescs.get(i)));
				supDescs.set(i, newc);
			}
			supDesc = factory.getOWLObjectUnionOf(new HashSet<OWLClassExpression>(supDescs));
		}

		if (!subDesc.isOWLNothing() && !supDesc.isOWLThing()) {
			axiomList.add(factory.getOWLSubClassOfAxiom(subDesc, supDesc));
			originList.add(originAxiom);
		}
	}

	private static boolean isNotOneOf(OWLClassExpression c) {
		return (c.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF &&
				((OWLObjectComplementOf)c).getOperand().getClassExpressionType() == ClassExpressionType.OBJECT_ONE_OF);
	}

	private static boolean isPosDescription(OWLClassExpression c) {
		if (c.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
			for (OWLClassExpression desc: c.asConjunctSet())
				if (!isPosDescription(desc))
					return false;
			return true;
		}
		else if (c.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)
			return isPosDescription(((OWLObjectSomeValuesFrom)c).getFiller());
		else if (c.getClassExpressionType() == ClassExpressionType.DATA_SOME_VALUES_FROM ||
				 c.getClassExpressionType() == ClassExpressionType.OWL_CLASS)
			return !c.isOWLNothing();
		return false;
	}

	private static boolean hasTwoOrMoreExistence(OWLObjectUnionOf or) {
		int i = 0;
        for (OWLClassExpression desc: or.getOperands())
            if (desc.getClassExpressionType() == ClassExpressionType.DATA_ALL_VALUES_FROM ||
            	desc.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)
                i++;
        return (i >= 2);
	}

}

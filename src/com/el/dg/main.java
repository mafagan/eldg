package com.el.dg;

import java.awt.geom.Area;
import java.io.File;
import java.io.FileNotFoundException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.*;

import de.tudresden.inf.lat.jcel.coreontology.axiom.NormalizedIntegerAxiom;
import de.tudresden.inf.lat.jcel.owlapi.main.JcelReasoner;
import de.tudresden.inf.lat.jcel.owlapi.translator.TranslationRepository;
import de.tudresden.inf.lat.jcel.reasoner.main.RuleBasedReasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import utils.LOG;
import utils.Literal;
import utils.LogicalRule;

import javax.print.attribute.standard.MediaSize;

public class main {

	/**
	 * @param args
	 * @throws SQLException
	 * @throws ClassNotFoundException
	 */
	public static final String url = "jdbc:mysql://localhost/eldg";
	public static final String user = "root";
	public static final String password = "1";
	public static final String ONT_FILE = "big0.owl";

	public void test() throws OWLOntologyCreationException {
		File ontFile = new File("test.owl");
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		manager.setSilentMissingImportsHandling(true);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(ontFile);
//
//		JcelReasoner reasoner = new JcelReasoner(ontology, false);
//		RuleBasedReasoner ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();
//
//		TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();
//
//		Set<NormalizedIntegerAxiom> normalizedIntegerAxiomSet = ruleBasedReasoner.getNormalizedIntegerAxiomSet();
//
//		Map<Integer, OWLClass> map = translatorReposity.getClassMap();
//		Iterator<Integer> itt = map.keySet().iterator();
//		while (itt.hasNext()){
//			Integer intt = itt.next();
//			LOG.info(intt + " " + map.get(intt));
//		}
//
//
//		Iterator<NormalizedIntegerAxiom> iterator = normalizedIntegerAxiomSet.iterator();
//
//		while (iterator.hasNext()){
//			String str = iterator.next().toString();
//			LOG.info(str);
//		}
	}

	public static void main(String[] args) throws SQLException, ClassNotFoundException, FileNotFoundException, OWLOntologyCreationException {
		// TODO Auto-generated method stub
//		Class.forName("com.mysql.jdbc.Driver");
//		Connection dbConnection = DriverManager.getConnection("jdbc:mysql://localhost/test",
//				"root", "");
//
//		Statement stmt = dbConnection.createStatement();
//		ResultSet rt = stmt.executeQuery("select * from predicate");
//		while (rt.next()) {
//			System.out.println(rt.getString(3));
//		}
//		dbConnection.close();


		/* init logging system */
		LOG.flag = true;

		if (false){
<<<<<<< HEAD
			return;
		}


=======
			/* test data */
			long startTime = System.currentTimeMillis();
			for (int i = 0; i < 10000; i++) {
				LOG.info("heihei");
			}
			long endTime = System.currentTimeMillis();
			LOG.info(endTime-startTime);
			return;
		}
		
		
>>>>>>> adfb44697849e3a750ffd26bb151134b3a3969b5
		if (LOG.flag){
			LOG.info("Logging module loaded.\n");
		}

		LOG.info("Loading TBox...");
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		//manager.setSilentMissingImportsHandling(true);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(ONT_FILE));

		LOG.info("Load completely.\n");
<<<<<<< HEAD

		long startTime = System.currentTimeMillis();



		PatternGeneration patternGeneration = new PatternGeneration(ontology);
		patternGeneration.doGenerate();

		long endTime = System.currentTimeMillis();
		long during = endTime-startTime;

//		LOG.info("Saving patterns...");
//		patternGeneration.savePattern();
//		LOG.info("Completely.");

		LOG.info("Program consumes " + during/1000 + "s.");

=======
		
		long startTime = System.currentTimeMillis();
		
		
		
		PatternGeneration patternGeneration = new PatternGeneration(ontology);
		patternGeneration.doGenerate();
		
		long endTime = System.currentTimeMillis();
		long during = endTime-startTime;
		
//		LOG.info("Saving patterns...");
//		patternGeneration.savePattern();
//		LOG.info("Completely.");
		
		LOG.info("Program consumes " + during/1000 + "s.");
		
>>>>>>> adfb44697849e3a750ffd26bb151134b3a3969b5
//		IRI likeIri = IRI.create("http://danye.me/like");
//		Literal body1 = new Literal(likeIri, new String[]{"?A", "?B", "?C"});
//		Literal body2 = new Literal(likeIri, new String[]{"?B", "?C", "?D"});
//		Literal head = new Literal(likeIri, new String[]{"?A", "?B", "?D"});
//
//		LogicalRule rule = new LogicalRule();
//		rule.head.add(head);
//		rule.body.add(body1);
//		rule.body.add(body2);
//
//		List<LogicalRule> ruleList = new ArrayList<LogicalRule>();
//		ruleList.add(rule);
//		TBoxCP generator = new TBoxCP(url, user, password, ontology);
		//generator.addRule(rule);
//		generator.setup(ruleList);
//		generator.computeCompletion();
//		generator.createCompletionTable();

	}

}

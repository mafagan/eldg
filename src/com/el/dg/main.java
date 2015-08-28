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

public class main {

	/**
	 * @param args
	 * @throws SQLException 
	 * @throws ClassNotFoundException 
	 */
	public static final String url = "jdbc:mysql://localhost/eldg";
	public static final String user = "root";
	public static final String password = "1";
	public static final String ONT_FILE = "ont.owl";

	public void test() throws OWLOntologyCreationException {
		File ontFile = new File("test.owl");
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		manager.setSilentMissingImportsHandling(true);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(ontFile);

		JcelReasoner reasoner = new JcelReasoner(ontology, false);
		RuleBasedReasoner ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();

		TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();

		Set<NormalizedIntegerAxiom> normalizedIntegerAxiomSet = ruleBasedReasoner.getNormalizedIntegerAxiomSet();

		Map<Integer, OWLClass> map = translatorReposity.getClassMap();
		Iterator<Integer> itt = map.keySet().iterator();
		while (itt.hasNext()){
			Integer intt = itt.next();
			LOG.info(intt + " " + map.get(intt));
		}


		Iterator<NormalizedIntegerAxiom> iterator = normalizedIntegerAxiomSet.iterator();

		while (iterator.hasNext()){
			String str = iterator.next().toString();
			LOG.info(str);
		}
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
		main test = new main();
		test.test();
		if (true)
			return;

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		manager.setSilentMissingImportsHandling(true);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(ONT_FILE));
		IRI likeIri = IRI.create("http://danye.me/like");
		Literal body1 = new Literal(likeIri, new String[]{"?A", "?B", "?C"});
		Literal body2 = new Literal(likeIri, new String[]{"?B", "?C", "?D"});
		Literal head = new Literal(likeIri, new String[]{"?A", "?B", "?D"});
		
		LogicalRule rule = new LogicalRule();
		rule.head.add(head);
		rule.body.add(body1);
		rule.body.add(body2);
		
		List<LogicalRule> ruleList = new ArrayList<LogicalRule>();
		ruleList.add(rule);
		TBoxCP generator = new TBoxCP(url, user, password, ontology);
		//generator.addRule(rule);
//		generator.setup(ruleList);
//		generator.computeCompletion();
//		generator.createCompletionTable();
		
	}

}

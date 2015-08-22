/**
 * Computes an approximate ABox completion by translating the TBox into a set of
 * definite rules and grounding the translated rules. When the TBox and the ABox
 * are expressed in the DLP fragment of OWL 2 DL, namely the OWL 2 RL profile
 * without global restrictions, the computation is exact.
 */
package generator;

import java.io.File;
import java.io.FileInputStream;
import java.io.PrintStream;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.TreeSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import utils.IntArrayComparator;
import utils.Literal;
import utils.LogicalRule;
import utils.OWL2Rule;

/**
 * @author Jianfeng Du
 *
 */
public class ABoxCompletionGenerator {

	final private static String ctable = 
		"(id int not null, " +
		"node int not null, " +
		"is_new tinyint null, " +
		"primary key (id), " +
		"unique (node), " +
		"index (is_new))";
	final private static String rtable = 
		"(id int not null, " +
		"fnode int not null, " +
		"tnode int not null, " +
		"is_new tinyint null, " +
		"primary key (id), " +
		"unique (fnode,tnode), " +
		"unique (tnode,fnode), " +
		"index (is_new))";
	final private static IRI HU_IRI = IRI.create("http://localhost/HU");
	final private static int HU_PID = -1;
	final private static String[] MAP_BIND = {"node", "fnode", "tnode"};
	final private static String TEMP_FILE = "temp.txt";
	final private static int MAX_PREDICATE_SHOWN = 5;

	final public static int FLAG_TEMPORARY = -1;
	final public static int FLAG_CONCEPT = 0;
	final public static int FLAG_ABSTRACT_ROLE = 1;
	final public static int FLAG_STRING_ROLE = 2;
	final public static int FLAG_INTEGER_ROLE = 3;
	final public static int FLAG_REAL_ROLE = 4;
	final public static int FLAG_SAME_AS = 5;

	private Connection dbConnection;
	private String[] indURIs;
	private String[] predURIs;
	private int[] predFlags;
	private List<String> stringList;
	private Set<Integer> intSet;
	private Set<Integer> realSet;
	private Map<String,Integer> indMap;
	private Map<String,int[]> predMap;
	private Map<String,Integer> stringMap;
	private OWLAxiom[] tboxAxioms;
	private int numAssertions;

	/**
	 * Constructor
	 * @param driver the driver for connecting to the database
	 * @param url	 the URL of the database
	 * @param user	 a valid user who can access the database 
	 * @param pwd	 the corresponding password of the user
	 * @throws Exception 
	 */
	public ABoxCompletionGenerator(String driver, String url, String user, String pwd) throws Exception {
		Class.forName(driver);
        dbConnection = DriverManager.getConnection(url, user, pwd);
        dbConnection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
        Statement stmt = dbConnection.createStatement();
        stmt.execute("set session read_buffer_size=41943040"); // 40M
        stmt.execute("set session read_rnd_buffer_size=41943040"); // 40M
        stmt.execute("set session sort_buffer_size=167772160"); // 160M
        stmt.execute("set session join_buffer_size=167772160"); // 160M
        stmt.close();
        if (!dbConnection.getAutoCommit())
			dbConnection.commit();
	}

	/**
	 * @param args
	 * @throws Exception 
	 */
	public static void main(String[] args) throws Exception {
		if (args.length < 2 || args.length > 3) {
			System.out.println("Usage java generator.ABoxCompletionGenerator <db> <owl file> [-reload]");
			return;
		}

		long st_time = System.currentTimeMillis();
		Properties props = new Properties();
        props.load(new FileInputStream("mysql.ini"));
        String host = props.getProperty("host", "localhost");
        String dbUser = props.getProperty("user");
        String dbPass = props.getProperty("password");
		ABoxCompletionGenerator generator = new ABoxCompletionGenerator(
				"com.mysql.jdbc.Driver", "jdbc:mysql://" + host + "/" + args[0], dbUser, dbPass);

		List<LogicalRule> rules = new ArrayList<LogicalRule>();
		OWLOntology ontology = generator.setupOntology(args[1], rules);
		if (args.length == 3 && args[2].equalsIgnoreCase("-reload"))
			generator.restoreCompletion();
		else
			generator.computeCompletion(ontology, rules);
		generator.createCompletionTable();
		generator.getDatabaseConnection().close();

		long ed_time = System.currentTimeMillis();
        long total_mem = Runtime.getRuntime().totalMemory();
        long free_mem = Runtime.getRuntime().freeMemory();
        System.out.printf("Finished in %d ms using %d bytes (JVM %d bytes)%n",
        		ed_time-st_time, total_mem-free_mem, total_mem);
        
//        for (int i = 0; i < generator.getTboxAxioms().length; i++) {
//			System.out.println(generator.getTboxAxioms()[i]);
//		}
        
//        Iterator<String> iterator = generator.getIndividualMap().keySet().iterator();
//        while (iterator.hasNext()) {
//        	String key = iterator.next();
//			System.out.println(key + " " + generator.getIndividualMap().get(key));
//		}
//        
//        System.out.println();
//        
//        Iterator<String> iterator2 = generator.getPredicateMap().keySet().iterator();
//        while (iterator2.hasNext()) {
//        	String key = iterator2.next();
//			System.out.print(key + " ");
//			
//			for (int i = 0; i < generator.getPredicateMap().get(key).length; i++) {
//				System.out.print(generator.getPredicateMap().get(key)[i] + " ");
//			}
//			System.out.println();
//		}
	}

	/**
	 * Creates the completion table for storing all assertions in the ABox completion.
	 * @throws Exception 
	 */
	public void createCompletionTable() throws Exception {
		Statement stmt = dbConnection.createStatement();

		stmt.execute("drop table if exists completion");
		stmt.execute("create table completion(" +
				"subject_id int not null, predicate_id int not null, " +
				"object_id int not null, index (subject_id))");
		if (!dbConnection.getAutoCommit())
			dbConnection.commit();

		for (int i = 0; i < predFlags.length; i++)
		if (predFlags[i] != FLAG_TEMPORARY && predFlags[i] != FLAG_SAME_AS) {
			PrintStream out = new PrintStream(TEMP_FILE);
			if (predFlags[i] == FLAG_CONCEPT) {
				ResultSet rs = stmt.executeQuery("select node from p" + (i+1));
				while (rs.next()) {
					out.print(rs.getInt(1));
					out.print("\t0\t");
					out.println(i+1);
				}
				rs.close();
			}
			else {
				ResultSet rs = stmt.executeQuery("select fnode,tnode from p" + (i+1));
				while (rs.next()) {
					out.print(rs.getInt(1));
					out.print('\t');
					out.print(i+1);
					out.print('\t');
					out.println(rs.getInt(2));
				}
				rs.close();
			}
			out.close();
			stmt.execute("load data local infile '" + TEMP_FILE + "' ignore into table completion");
			if (!dbConnection.getAutoCommit())
				dbConnection.commit();
		}

		(new File(TEMP_FILE)).delete();
		stmt.close();
	}

	/**
	 * Setups data for predicates, individuals and literals in the given ontology
	 * @param fileName	the name of the ontology file
	 * @param rules		the list of definite rules translated from the ontology
	 * @return the ontology read from the given ontology file
	 * @throws Exception
	 */
	public OWLOntology setupOntology(String fileName, List<LogicalRule> rules) throws Exception {
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		manager.setSilentMissingImportsHandling(true);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(fileName));
		rules.clear();
		rules.addAll(OWL2Rule.translate(ontology, false, true));
		
		
		/************** add my rule  ********************/
		
//		for(OWLAxiom ax:ontology.getAxioms()){
//			System.out.println(ax);
//		}
		IRI predIri = IRI.create("http://danye.me/like");
		Literal head = new Literal(predIri, new String[]{"?X", "?Z"});
		Literal body1 = new Literal(predIri, new String[]{"?X", "?Y"});
		Literal body2 = new Literal(predIri, new String[]{"?Y", "?Z"});
		LogicalRule mrule = new LogicalRule();
		mrule.head.add(head);
		mrule.body.add(body1);
		mrule.body.add(body2);
		rules.add(mrule);
		
		/**********************************/

		removeInvaidRules(rules);
		
		System.out.printf("Loaded ontology %s (totally %d logical axioms, translated to %d rules).%n",
				fileName, ontology.getLogicalAxiomCount(), rules.size());

		// Setup data for predicates
		predMap = new TreeMap<String,int[]>();
		//predMap.put(OWL2Rule.DATA_EQUAL_IRI.toString(), new int[] {OWL2Rule.DATA_EQUAL_PID, FLAG_SAME_AS});
		//predMap.put(OWL2Rule.EQUAL_IRI.toString(), new int[] {OWL2Rule.EQUAL_PID, FLAG_SAME_AS});
		predMap.put(OWL2Rule.NOT_EQUAL_IRI.toString(), new int[] {OWL2Rule.NOT_EQUAL_PID, FLAG_SAME_AS});
		predMap.put(OWL2Rule.UNIFORM_EQ_IRI.toString(), new int[] {OWL2Rule.EQUAL_PID, FLAG_SAME_AS});
		
		
		initPredicates(ontology, rules);
		
		predURIs = new String[predMap.size()];
		predFlags = new int[predMap.size()];
		for (Entry<String,int[]> entry: predMap.entrySet()) {
			predURIs[entry.getValue()[0]-1] = entry.getKey();
			predFlags[entry.getValue()[0]-1] = entry.getValue()[1];
		}
		
		// Setup data for individuals and literals
		setupIndividuals(ontology);
		setupLiterals(ontology);
		manager.removeOntology(ontology);
		
		// Setup axioms in the TBox
		Map<OWLAxiom,Integer> axiomMap = new TreeMap<OWLAxiom,Integer>();
		for (LogicalRule rule: rules)
		if (rule.origin != null) {
			Integer rid = axiomMap.get(rule.origin);
			if (rid == null) {
				rid = new Integer(axiomMap.size()+1);
				axiomMap.put(rule.origin, rid);
			}
			rule.originAID = rid.intValue();
		}
		tboxAxioms = new OWLAxiom[axiomMap.size()];
		for (Entry<OWLAxiom,Integer> entry: axiomMap.entrySet())
			tboxAxioms[entry.getValue().intValue()-1] = entry.getKey();

		return ontology;
	}

	private void setupLiterals(OWLOntology ontology) {
		stringList = new ArrayList<String>();
		stringMap = new TreeMap<String,Integer>();
		intSet = new HashSet<Integer>();
		realSet = new HashSet<Integer>();

		for (OWLNegativeDataPropertyAssertionAxiom ax: ontology.getAxioms(AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION)) {
			OWLDataProperty dp = ax.getProperty().asOWLDataProperty();
			int[] data = predMap.get(dp.getIRI().toString());
			if (data != null) { // it should be such
				if (data[1] == FLAG_INTEGER_ROLE)
					intSet.add(ax.getObject().parseInteger());
				else if (data[1] == FLAG_REAL_ROLE)
					realSet.add((int) Math.round(ax.getObject().parseDouble()*100));
				else if (!stringMap.containsKey(ax.getObject().getLiteral())) {
					stringList.add(ax.getObject().getLiteral());
					stringMap.put(ax.getObject().getLiteral(), stringList.size());
				}
			}
		}

		for (OWLDataPropertyAssertionAxiom ax: ontology.getAxioms(AxiomType.DATA_PROPERTY_ASSERTION)) {
			OWLDataProperty dp = ax.getProperty().asOWLDataProperty();
			int[] data = predMap.get(dp.getIRI().toString());
			if (data != null) { // it should be such
				if (data[1] == FLAG_INTEGER_ROLE)
					intSet.add(ax.getObject().parseInteger());
				else if (data[1] == FLAG_REAL_ROLE)
					realSet.add((int) Math.round(ax.getObject().parseDouble()*100));
				else if (!stringMap.containsKey(ax.getObject().getLiteral())) {
					stringList.add(ax.getObject().getLiteral());
					stringMap.put(ax.getObject().getLiteral(), stringList.size());
				}
			}
		}
	}

	/**
	 * Restores the ABox completion from the database.
	 * Either this method is called, or the method ComputeCompletion is called.
	 * @throws SQLException 
	 */
	public void restoreCompletion() throws SQLException {
		numAssertions = 0;
		int[] numInstances = new int[MAX_PREDICATE_SHOWN];
		int[] shownIndices = new int[MAX_PREDICATE_SHOWN];
		int count = 0;
		Statement stmt = dbConnection.createStatement(ResultSet.TYPE_FORWARD_ONLY, ResultSet.CONCUR_READ_ONLY);
		for (int i = 0; i < predFlags.length; i++) {
			ResultSet rs = stmt.executeQuery(String.format("select max(id),count(id) from p%d where is_new<=1", i+1));
			if (rs.next()) {
				int maxid = rs.getInt(1);
				if (maxid > numAssertions)
					numAssertions = maxid;
				if (predFlags[i] == FLAG_CONCEPT) {
					int num = rs.getInt(2);
					int k = count-1;
					while (k >= 0 && numInstances[k] < num) {
						if (k < MAX_PREDICATE_SHOWN-1) {
							numInstances[k+1] = numInstances[k];
							shownIndices[k+1] = shownIndices[k];
						}
						k--;
					}
					k++;
					if (k < MAX_PREDICATE_SHOWN) {
						numInstances[k] = num;
						shownIndices[k] = i;
					}
					if (count < MAX_PREDICATE_SHOWN)
						count++;
				}
			}
			rs.close();
		}
		stmt.close();
		System.out.printf("Reloaded %d assertions.%n", numAssertions);
		System.out.printf("The top %d concepts that have the maximal number of instances:%n", MAX_PREDICATE_SHOWN);
		for (int i = 0; i < count; i++)
			System.out.printf("%s [%d]%n", predURIs[shownIndices[i]], numInstances[i]);
	}

	/**
	 * Computes the ABox completion and stores it into the database.
	 * @param ontology	the given ontology
	 * @param rules 	the list of definite rules translated from the given ontology
	 * @throws Exception
	 */
	public void computeCompletion(OWLOntology ontology, List<LogicalRule> rules) throws Exception {
		//boolean seenEqual = false;
		//boolean seenDataEqual = false;
		boolean addedHU = false;
		for (LogicalRule rule: rules) {
			//System.out.println(rule + " " + rule.head.get(0).id);
			// Make the rule safe and add an accessory body item for every equational head atom
			/*if (rule.head.get(0).id == OWL2Rule.DATA_EQUAL_PID) {
				seenDataEqual = true;
				Literal atom = new Literal(OWL2Rule.NOT_EQUAL_IRI, rule.head.get(0).arguments);
				atom.id = OWL2Rule.NOT_EQUAL_PID;
				rule.body.add(atom);
			}
			else if (rule.head.get(0).id == OWL2Rule.EQUAL_PID) {
				seenEqual = true;
				Literal atom = new Literal(OWL2Rule.NOT_EQUAL_IRI, rule.head.get(0).arguments);
				atom.id = OWL2Rule.NOT_EQUAL_PID;
				rule.body.add(atom);
			}*/
//			if (rule.head.get(0).id != OWL2Rule.EQUAL_PID) {
//				for (int i = 0; i < rule.head.get(0).arguments.length; i++)
//				if (rule.head.get(0).arguments[i].startsWith("?")) {
//					int k = rule.body.size()-1;
//					while (k >= 0 && !rule.body.get(k).arguments[0].equals(rule.head.get(0).arguments[i]))
//						k--;
//					if (k < 0) {
//						addedHU = true;
//						Literal atom = new Literal(HU_IRI, new String[] {rule.head.get(0).arguments[i]});
//						atom.id = HU_PID;
//						rule.body.add(atom);
//					}
//				}
//			}
			// Replace individuals or literals with numbers  
			replaceConstants(rule.head);
        	replaceConstants(rule.body);
		}

		
		/*
		// Append rules for axiomatizing equality and compose SQL sentences for all rules
		String ontologyBase = ontology.getOntologyID().getOntologyIRI().toString();
		if (!ontologyBase.endsWith("#"))
			ontologyBase = ontologyBase + "#";
		appendEqualityRules(rules, seenEqual, seenDataEqual, ontologyBase);
		*/
		for (LogicalRule rule: rules)
			composeSQL(rule);

		Statement stmt = dbConnection.createStatement();

		// Create the predicate table
		stmt.execute("drop table if exists predicate");
		stmt.execute("create table predicate(id int not null, " +
				"flag tinyint null, name varchar(255) null, " +
				"primary key (id), index (flag), index (name))");
		if (!dbConnection.getAutoCommit())
			dbConnection.commit();
		PrintStream out = new PrintStream(TEMP_FILE);
		for (int i = 0; i < predURIs.length; i++) {
			out.print(i+1);
			out.print('\t');
			out.print(predFlags[i]);
			out.print('\t');
			out.println(predURIs[i]);
		}
		out.close();
		stmt.execute(String.format("load data local infile '%s' ignore into " +
				"table predicate lines terminated by '\\r\\n'", TEMP_FILE));
		if (!dbConnection.getAutoCommit())
			dbConnection.commit();

		// Create the HU table
		if (addedHU) {
			stmt.execute("drop table if exists hu");
			stmt.execute("create table hu" + ctable);
			if (!dbConnection.getAutoCommit())
				dbConnection.commit();
			out = new PrintStream(TEMP_FILE);
			for (int i = 0; i < indURIs.length; i++) {
				out.print(i+1);
				out.print('\t');
				out.print(i+1);
				out.println("\t0");
			}
			out.close();
			stmt.execute(String.format("load data local infile '%s' ignore into table hu", TEMP_FILE));
			if (!dbConnection.getAutoCommit())
				dbConnection.commit();
		}

		// Store assertions in the given ontology into the database
		storeAssertions(ontology, stmt);
		System.out.print("Computing the ABox completion.");

		stmt.close();

		// Compute the least model
		boolean[] orgTrigger = null;
		boolean[] newTrigger = new boolean[predFlags.length];
		int orgNumFacts = 0;
		while (numAssertions > orgNumFacts) {
			System.out.print('.');
			orgNumFacts = numAssertions;
			for (LogicalRule rule: rules)
				processRule(rule, orgTrigger, newTrigger);

			stmt = dbConnection.createStatement();
			if (orgTrigger != null) {
				for (int i = 0; i < orgTrigger.length; i++)
					if (orgTrigger[i])
						stmt.execute(String.format("update p%d set is_new=1 where is_new=2", i+1));
				if (!dbConnection.getAutoCommit())
					dbConnection.commit();
			}
			if (numAssertions > orgNumFacts) {
				for (int i = 0; i < newTrigger.length; i++)
					if (newTrigger[i])
						stmt.execute(String.format("update p%d set is_new=2 where is_new=3", i+1));
				if (!dbConnection.getAutoCommit())
					dbConnection.commit();
			}
			stmt.close();

			orgTrigger = newTrigger;
			newTrigger = new boolean[orgTrigger.length];
		}
		System.out.printf("obtained %d assertions.%n", numAssertions);

		(new File(TEMP_FILE)).delete();
	}

	/**
	 * Adds new assertions instantiated from the given rule to the database.  
	 * @param rule		 a definite rule translated from the ontology
	 * @param orgTrigger the i-th value indicating whether new assertions on the i+1-th predicate have been added
	 * @param newTrigger the i-th value indicating whether new assertions on the i+1-th predicate are added
	 * @throws Exception
	 */
	private void processRule(LogicalRule rule, boolean[] orgTrigger, boolean[] newTrigger) throws Exception {
		Statement stmt = dbConnection.createStatement(ResultSet.TYPE_FORWARD_ONLY, ResultSet.CONCUR_READ_ONLY);
		TreeSet<int[]> keySet = new TreeSet<int[]>(new IntArrayComparator());
		
		PrintStream out = new PrintStream(TEMP_FILE);
		int ps = 0;
		while (ps < rule.body.size()) {
			if (orgTrigger != null)
			while (ps < rule.body.size() && (rule.body.get(ps).id == OWL2Rule.NOT_EQUAL_PID || 
					rule.body.get(ps).id == HU_PID || !orgTrigger[rule.body.get(ps).id-1]))
				ps++;

			if (orgTrigger == null || ps < rule.body.size()) {
				boolean first = false;
				StringBuffer sqlBuf = new StringBuffer(rule.sql);
				if (rule.sql.indexOf(" where ") < 0) {
					sqlBuf.append(" where ");
					first = true;
				}
				if (orgTrigger == null) {
					for (int i = 0; i < rule.body.size(); i++)
					if (rule.body.get(i).id != OWL2Rule.NOT_EQUAL_PID) {
						if (first)
							first = false;
						else
							sqlBuf.append(" and ");
						sqlBuf.append(String.format("b%d.is_new<3", i));
					}
				}
				else {
					for (int i = 0; i < rule.body.size(); i++)
					if (rule.body.get(i).id != OWL2Rule.NOT_EQUAL_PID) {
						if (first)
							first = false;
						else
							sqlBuf.append(" and ");
						if (i < ps)
							sqlBuf.append(String.format("b%d.is_new<2", i));
						else if (i == ps)
							sqlBuf.append(String.format("b%d.is_new=2", i));
						else
							sqlBuf.append(String.format("b%d.is_new<3", i));
					}
				}

				ResultSet rs = stmt.executeQuery(sqlBuf.toString());
				while (rs.next()) {
					if (rs.getInt("hid0") == 0) { // probably a new record
						int[] key = new int[2];
						for (int i = 0; i < rule.head.get(0).arguments.length; i++) {
							if (rule.head.get(0).arguments[i].startsWith("?"))
								key[i] = rs.getInt(rule.head.get(0).arguments[i].substring(1));
							else
								key[i] = Integer.parseInt(rule.head.get(0).arguments[i]);
						}
						if (!keySet.contains(key)) { // a really new record
							keySet.add(key);
							out.print(++numAssertions);
							for (int i = 0; i < rule.head.get(0).arguments.length; i++) {
								out.print('\t');
								out.print(key[i]);
							}
		                	out.println("\t3");
						}
					}
				}
				rs.close();
			}

			if (orgTrigger == null)
				break;
			ps++;
		}
		out.close();

		if (keySet.size() > 0) {
			newTrigger[rule.head.get(0).id-1] = true;
			stmt.execute(String.format("load data local infile '%s' ignore into table p%d",
					TEMP_FILE, rule.head.get(0).id));
	        if (!dbConnection.getAutoCommit())
	        	dbConnection.commit();
		}

		stmt.close();
	}

	/**
	 * Stores assertions in the given ontology into the database.
	 * @param ontology	the given ontology
	 * @param stmt		the database statement object for manipulating the database
	 * @throws Exception
	 */
	private void storeAssertions(OWLOntology ontology, Statement stmt) throws Exception {
		@SuppressWarnings("unchecked")
		ArrayList<int[]>[] assertions = new ArrayList[predFlags.length];

		for (OWLClassAssertionAxiom axiom: ontology.getAxioms(AxiomType.CLASS_ASSERTION)) {
			OWLClassExpression expr = axiom.getClassExpression().getNNF();
			if (expr instanceof OWLClass) {
				int[] data = predMap.get(expr.asOWLClass().getIRI().toString());
				if (data != null) { // it should be such
					if (assertions[data[0]-1] == null)
						assertions[data[0]-1] = new ArrayList<int[]>();
					Integer num = indMap.get(axiom.getIndividual().asOWLNamedIndividual().getIRI().toString());
					if (num != null) // it should be such
						assertions[data[0]-1].add(new int[] {num.intValue()});
				}
			}
		}

		for (OWLObjectPropertyAssertionAxiom axiom: ontology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION)) {
			OWLObjectProperty op = axiom.getProperty().asOWLObjectProperty();
			int[] data = predMap.get(op.getIRI().toString());
			if (data != null) { // it should be such
				if (assertions[data[0]-1] == null)
					assertions[data[0]-1] = new ArrayList<int[]>();
				Integer num1 = indMap.get(axiom.getSubject().asOWLNamedIndividual().getIRI().toString());
				Integer num2 = indMap.get(axiom.getObject().asOWLNamedIndividual().getIRI().toString());
				if (num1 != null && num2 != null) // it should be such
					assertions[data[0]-1].add(new int[] {num1.intValue(), num2.intValue()});
			}
		}

		for (OWLDataPropertyAssertionAxiom axiom: ontology.getAxioms(AxiomType.DATA_PROPERTY_ASSERTION)) {
			OWLDataProperty dp = axiom.getProperty().asOWLDataProperty();
			int[] data = predMap.get(dp.getIRI().toString());
			if (data != null) { // it should be such
				if (assertions[data[0]-1] == null)
					assertions[data[0]-1] = new ArrayList<int[]>();
				int value = 0;
				if (data[1] == FLAG_INTEGER_ROLE)
					value = axiom.getObject().parseInteger();
				else if (data[1] == FLAG_REAL_ROLE)
					value = (int) Math.round(axiom.getObject().parseDouble()*100); 
				else {
					Integer num = stringMap.get(axiom.getObject().getLiteral());
					if (num != null) // it should be such
						value = num.intValue();
				}
				Integer num = indMap.get(axiom.getSubject().asOWLNamedIndividual().getIRI().toString());				
				if (num != null) // it should be such
					assertions[data[0]-1].add(new int[] {num.intValue(), value});
			}
		}

		numAssertions = 0;
		for (int i = 0; i < predFlags.length; i++) {
			stmt.execute(String.format("drop table if exists p%d", i+1));
			if (predFlags[i] == FLAG_TEMPORARY || predFlags[i] == FLAG_CONCEPT)
				stmt.execute(String.format("create table p%d%s", i+1, ctable));
			else
				stmt.execute(String.format("create table p%d%s", i+1, rtable));
			if (!dbConnection.getAutoCommit()) 
				dbConnection.commit();
			if (assertions[i] != null) {
				PrintStream out = new PrintStream(TEMP_FILE);
				for (int[] values: assertions[i]) {
					out.print(++numAssertions);
					out.print('\t');
					for (int j = 0; j < values.length; j++) {
						out.print(values[j]);
						out.print('\t');
					}
					out.println('0');
				}
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, i+1));
				if (!dbConnection.getAutoCommit())
					dbConnection.commit();
			}
		}

		System.out.printf("Totally %d individuals and %d ABox assertions.%n", indURIs.length, numAssertions);
	}

	private void composeSQL(LogicalRule rule) {
		StringBuffer sqlBuf = new StringBuffer();
		StringBuffer condBuf = new StringBuffer();
		// atom_index * 3 + type (node=0, fnode=1, tnode=2)
		Map<String,Integer> varBind = new HashMap<String,Integer>();

		for (int i = 0; i < rule.body.size(); i++)
		if (rule.body.get(i).id == OWL2Rule.NOT_EQUAL_PID) {
			Integer bind1 = varBind.get(rule.body.get(i).arguments[0]);
			if (bind1 == null) {
				System.out.printf("%s should appear earlier in %s%n", rule.body.get(i).arguments[0], rule);
				return;
			}
			Integer bind2 = varBind.get(rule.body.get(i).arguments[1]);
			if (bind2 == null) {
				System.out.printf("%s should appear earlier in %s%n", rule.body.get(i).arguments[1], rule);
				return;
			}
			int v1 = bind1.intValue();
			int v2 = bind2.intValue();
			if (v1 > v2) {
				int v = v1;
				v1 = v2;
				v2 = v;
			}
			if (v1 != v2) {
				if (condBuf.length() == 0)
					condBuf.append(" where ");
				else
					condBuf.append(" and ");
				condBuf.append(String.format("b%d.%s<b%d.%s", 
						bind_atom(v1), MAP_BIND[bind_type(v1)],
						bind_atom(v2), MAP_BIND[bind_type(v2)]));
			}
		}
		else {
			// Handle the first term
			if (rule.body.get(i).arguments[0].startsWith("?")) {
				Integer bind = varBind.get(rule.body.get(i).arguments[0]);
				if (bind != null) {
					int v = bind.intValue();
					if (condBuf.length() == 0)
						condBuf.append(" where ");
					else
						condBuf.append(" and ");
					condBuf.append(String.format("b%d.%s=b%d.%s", i,
							(rule.body.get(i).arguments.length == 1)? "node": "fnode",
							bind_atom(v), MAP_BIND[bind_type(v)]));
				}
				else {
					int v = make_bind(i, rule.body.get(i).arguments.length-1);
					varBind.put(rule.body.get(i).arguments[0], v);
				}
			}
			else {
				if (condBuf.length() == 0)
					condBuf.append(" where ");
				else
					condBuf.append(" and ");
				condBuf.append(String.format("b%d.%s=%s", i,
						(rule.body.get(i).arguments.length == 1)? "node": "fnode", rule.body.get(i).arguments[0]));
			}
			// Handle the second term
			if (rule.body.get(i).arguments.length > 1)
			if (rule.body.get(i).arguments[1].startsWith("?")) {
				Integer bind = varBind.get(rule.body.get(i).arguments[1]);
				if (bind != null) {
					int v = bind.intValue();
					if (condBuf.length() == 0)
						condBuf.append(" where ");
					else
						condBuf.append(" and ");
					condBuf.append(String.format("b%d.tnode=b%d.%s", i,
							bind_atom(v), MAP_BIND[bind_type(v)]));
				}
				else {
					int v = make_bind(i, 2);
					varBind.put(rule.body.get(i).arguments[1], v);
				}
			}
			else {
				if (condBuf.length() == 0)
					condBuf.append(" where ");
				else
					condBuf.append(" and ");
				condBuf.append(String.format("b%d.tnode=%s", i, rule.body.get(i).arguments[1]));
			}
		}

		Set<Integer> binds = new HashSet<Integer>();
		for (int i = 0; i < rule.head.size(); i++)
		for (int j = 0; j < rule.head.get(i).arguments.length; j++)
		if (rule.head.get(i).arguments[j].startsWith("?")) {
			Integer bind = varBind.get(rule.head.get(i).arguments[j]);
			if (bind == null) {
				System.out.printf("%s should appear in the body of %s%n", rule.head.get(i).arguments[j], rule);
				return;
			}
			else if (!binds.contains(bind)) {
				binds.add(bind);
				int v = bind.intValue();
				if (sqlBuf.length() == 0)
					sqlBuf.append(String.format("select distinct b%d.%s as %s",
							bind_atom(v), MAP_BIND[bind_type(v)], rule.head.get(i).arguments[j].substring(1)));
				else
					sqlBuf.append(String.format(", b%d.%s as %s",
							bind_atom(v), MAP_BIND[bind_type(v)], rule.head.get(i).arguments[j].substring(1)));
			}
		}
		for (int i = 0; i < rule.head.size(); i++)
			sqlBuf.append(String.format(", h%d.id as hid%d", i, i));

		boolean hasFrom = false;
		for (int i = 0; i < rule.body.size(); i++)
		if (rule.body.get(i).id != OWL2Rule.NOT_EQUAL_PID) {
			if (hasFrom) {
				if (rule.body.get(i).id == HU_PID)
					sqlBuf.append(String.format(" cross join hu b%d", i));
				else
					sqlBuf.append(String.format(" cross join p%d b%d", rule.body.get(i).id, i));
			}
			else {
				if (rule.body.get(i).id == HU_PID)
					sqlBuf.append(String.format(" from hu b%d", i));
				else
					sqlBuf.append(String.format(" from p%d b%d", rule.body.get(i).id, i));
				hasFrom = true;
			}
		}

		for (int i = 0; i < rule.head.size(); i++) {
			sqlBuf.append(String.format(" left join p%d h%d on ", rule.head.get(i).id, i));
			// Handle the first term
			Integer bind = varBind.get(rule.head.get(i).arguments[0]);
			if (bind != null) {
				int v = bind.intValue();
				sqlBuf.append(String.format("h%d.%s=b%d.%s", i,
						(rule.head.get(i).arguments.length == 1)? "node": "fnode",
						bind_atom(v), MAP_BIND[bind_type(v)]));
			}
			else
				sqlBuf.append(String.format("h%d.%s=%s", i,
						(rule.head.get(i).arguments.length == 1)? "node": "fnode",
						rule.head.get(i).arguments[0]));
			// Handle the second term
			if (rule.head.get(i).arguments.length > 1)
			if ((bind = varBind.get(rule.head.get(i).arguments[1])) != null) {
				int v = bind.intValue();
				sqlBuf.append(String.format(" and h%d.tnode=b%d.%s", i,
						bind_atom(v), MAP_BIND[bind_type(v)]));
			}
			else
				sqlBuf.append(String.format("h%d.tnode=%s", i, rule.head.get(i).arguments[1]));
		}

		sqlBuf.append(condBuf.toString());
		rule.sql = sqlBuf.toString();
		
//		System.out.println(rule);
//		System.out.println(sqlBuf+"\n");
	}

	private int make_bind(int x, int t) {
		return x*3+t;
	}

	private int bind_type(int v) {
		return v%3;
	}

	private int bind_atom(int v) {
		return v/3;
	}

	/**
	 * Append rules that axiomatize equality to the given list of rules.
	 * @param rules			the list of rules to be updated
	 * @param seenDataEqual	whether data equality has been seen
	 * @param seenEqual 	whether equality has been seen
	 * @param base			the ontology base
	 */
	/*
	private void appendEqualityRules(List<LogicalRule> rules, boolean seenEqual, boolean seenDataEqual, String base) {
		for (Entry<String,int[]> entry: predMap.entrySet()) {
			int[] data = entry.getValue();
			if (data[1] == FLAG_CONCEPT && seenEqual) {
				LogicalRule rule = OWL2Rule.parseSentence(
						String.format("%s(?X):-%s(?Y),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
				rule.head.get(0).id = data[0];
				rule.body.get(0).id = data[0];
				rule.body.get(1).id = OWL2Rule.EQUAL_PID;
				rules.add(rule);
				rule = OWL2Rule.parseSentence(
						String.format("%s(?Y):-%s(?X),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
				rule.head.get(0).id = data[0];
				rule.body.get(0).id = data[0];
				rule.body.get(1).id = OWL2Rule.EQUAL_PID;
				rules.add(rule);
			}
			else if (data[1] == FLAG_ABSTRACT_ROLE && seenEqual) {
				LogicalRule rule = OWL2Rule.parseSentence(
						String.format("%s(?X,?Z):-%s(?Y,?Z),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
				rule.head.get(0).id = data[0];
				rule.body.get(0).id = data[0];
				rule.body.get(1).id = OWL2Rule.EQUAL_PID;
				rules.add(rule);
				rule = OWL2Rule.parseSentence(
						String.format("%s(?Y,?Z):-%s(?X,?Z),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
				rule.head.get(0).id = data[0];
				rule.body.get(0).id = data[0];
				rule.body.get(1).id = OWL2Rule.EQUAL_PID;
				rules.add(rule);
				rule = OWL2Rule.parseSentence(
						String.format("%s(?Z,?X):-%s(?Z,?Y),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
				rule.head.get(0).id = data[0];
				rule.body.get(0).id = data[0];
				rule.body.get(1).id = OWL2Rule.EQUAL_PID;
				rules.add(rule);
				rule = OWL2Rule.parseSentence(
						String.format("%s(?Z,?Y):-%s(?Z,?X),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
				rule.head.get(0).id = data[0];
				rule.body.get(0).id = data[0];
				rule.body.get(1).id = OWL2Rule.EQUAL_PID;
				rules.add(rule);
			}
			else if (data[1] == FLAG_STRING_ROLE || data[1] == FLAG_INTEGER_ROLE || data[1] == FLAG_REAL_ROLE) {
				if (seenEqual) {
					LogicalRule rule = OWL2Rule.parseSentence(
							String.format("%s(?X,?Z):-%s(?Y,?Z),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
					rule.head.get(0).id = data[0];
					rule.body.get(0).id = data[0];
					rule.body.get(1).id = OWL2Rule.EQUAL_PID;
					rules.add(rule);
					rule = OWL2Rule.parseSentence(
							String.format("%s(?Y,?Z):-%s(?X,?Z),EQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
					rule.head.get(0).id = data[0];
					rule.body.get(0).id = data[0];
					rule.body.get(1).id = OWL2Rule.EQUAL_PID;
					rules.add(rule);
				}
				if (seenDataEqual) {
					LogicalRule rule = OWL2Rule.parseSentence(
							String.format("%s(?Z,?X):-%s(?Z,?Y),DEQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
					rule.head.get(0).id = data[0];
					rule.body.get(0).id = data[0];
					rule.body.get(1).id = OWL2Rule.DATA_EQUAL_PID;
					rules.add(rule);
					rule = OWL2Rule.parseSentence(
							String.format("%s(?Z,?Y):-%s(?Z,?X),DEQ(?X,?Y).", entry.getKey(), entry.getKey()), base);
					rule.head.get(0).id = data[0];
					rule.body.get(0).id = data[0];
					rule.body.get(1).id = OWL2Rule.DATA_EQUAL_PID;
					rules.add(rule);
				}
			}
		}
	}
	*/

	private void replaceConstants(List<Literal> atoms) {
		for (int i = 0; i < atoms.size(); i++)
		for (int j = 0; j < atoms.get(i).arguments.length; j++)
		if (!atoms.get(i).arguments[j].startsWith("?")) {
			String name = atoms.get(i).arguments[j];
			if (name.startsWith("\"") && name.endsWith("\""))	{
        		Integer num = stringMap.get(name.substring(1, name.length()-1));
        		if (num == null)
                    System.out.printf("Cannot find %s in the ontology%n", name);
       			atoms.get(i).arguments[j] = String.valueOf(num);
        	}
        	else if (name.indexOf("://") >= 0) {
        		Integer num = indMap.get(name);
                if (num == null)
                    System.out.printf("Cannot find %s in the ontology%n", name);
               	atoms.get(i).arguments[j] = String.valueOf(num);
        	}
        	else if (name.indexOf('.') > 0)
        		atoms.get(i).arguments[j] =	String.valueOf((int)(Double.parseDouble(name)*100));
		}
	}

	/**
	 * Setups data for individuals in the ontology.
	 */
	private void setupIndividuals(OWLOntology ontology) {
		Set<OWLNamedIndividual> individuals = ontology.getIndividualsInSignature();
		indURIs = new String[individuals.size()];
        indMap = new TreeMap<String,Integer>();
        int i = 0;
        for (OWLNamedIndividual ind: individuals) {
            indURIs[i++] = ind.getIRI().toString();
            indMap.put(ind.getIRI().toString(), i);
        }
	}

	/**
	 * Initializes the map from predicate URIs to identifiers and flags.
	 * @param ontology	the given ontology
	 * @param rules		the list of definite rules translated from the ontology
	 */
	private void initPredicates(OWLOntology ontology, List<LogicalRule> rules) {
		// Deal with all atomic classes
		for (OWLClass c: ontology.getClassesInSignature())
		if (!c.isOWLThing() && !c.isOWLNothing()) {
			int[] data = predMap.get(c.getIRI().toString());
			if (data == null)
				predMap.put(c.getIRI().toString(), new int[]{predMap.size()+1, FLAG_CONCEPT});
		}

		// Deal with all object properties
		for (OWLObjectProperty op: ontology.getObjectPropertiesInSignature()) {
			int[] data = predMap.get(op.getIRI().toString());
			if (data == null)
				predMap.put(op.getIRI().toString(), new int[]{predMap.size()+1, FLAG_ABSTRACT_ROLE});
		}

		// Deal with all datatype properties
		for (OWLDataProperty dp: ontology.getDataPropertiesInSignature()) {
			int ftype = FLAG_STRING_ROLE;
			for (OWLDataRange range: dp.getRanges(ontology))
			if (range.isDatatype()) {
            	if (range.asOWLDatatype().isDouble() || range.asOWLDatatype().isFloat())
            		ftype = FLAG_REAL_ROLE;
            	else if (range.asOWLDatatype().isInteger())
            		ftype = FLAG_INTEGER_ROLE;
            	break;
            }
			int[] data = predMap.get(dp.getIRI().toString());
			if (data == null)
				predMap.put(dp.getIRI().toString(), new int[]{predMap.size()+1, ftype});
		}

		// Deal with other predicates in translated rules
		for (LogicalRule rule: rules) {
			int[] data = predMap.get(rule.head.get(0).predicate.toString());
			if (data == null) {
				data = new int[]{predMap.size()+1, FLAG_TEMPORARY};
				predMap.put(rule.head.get(0).predicate.toString(), data);
			}
			rule.head.get(0).id = data[0];
			for (int i = 0; i < rule.body.size(); i++) {
				data = predMap.get(rule.body.get(i).predicate.toString());
				if (data == null) {
					data = new int[]{predMap.size()+1, FLAG_TEMPORARY};
					predMap.put(rule.body.get(i).predicate.toString(), data);
				}
				rule.body.get(i).id = data[0];
			}
		}
	}

	/**
	 * Removes disjunctive rules, constraints, and rules with function symbols
	 * from the given list of rules.
	 * @param rules the given list of rules
	 */
	private void removeInvaidRules(List<LogicalRule> rules) {
		for (int i = rules.size()-1; i >= 0; i--)
		if (rules.get(i).head.size() > 1 || rules.get(i).body.size() == 0) {
			rules.remove(i);
		}
		else {
			boolean hasFuncSymbol = false;
			for (int j = 0; j < rules.get(i).head.size() && !hasFuncSymbol; j++) {
				String[] args = rules.get(i).head.get(j).arguments;
				for (int k = 0; k < args.length && !hasFuncSymbol; k++)
					if (args[k].startsWith("?f"))
						hasFuncSymbol = true;
			}
			for (int j = 0; j < rules.get(i).body.size() && !hasFuncSymbol; j++) {
				String[] args = rules.get(i).body.get(j).arguments;
				for (int k = 0; k < args.length && !hasFuncSymbol; k++)
					if (args[k].startsWith("?f"))
						hasFuncSymbol = true;
			}
			if (hasFuncSymbol)
				rules.remove(i);
		}
	}

	/**
	 * @return the database connection
	 */
	public Connection getDatabaseConnection() {
		return dbConnection;
	}

	/**
	 * @return the array of URIs of individuals in the ontology
	 */
	public String[] getIndividualURIs() {
		return indURIs;
	}

	/**
	 * @return the array of URIs of predicates (i.e. concepts/roles) in the ontology  
	 */
	public String[] getPredicateURIs() {
		return predURIs;
	}

	/**
	 * @return the array of flags of predicates (i.e. concepts/roles) in the ontology
	 */
	public int[] getPredicateFlags() {
		return predFlags;
	}

	/**
	 * @return the list of string literals in the ontology
	 */
	public List<String> getStringList() {
		return stringList;
	}

	/**
	 * @return the set of integer literals in the ontology
	 */
	public Set<Integer> getIntegerSet() {
		return intSet;
	}

	/**
	 * @return the set of real literals in the ontology
	 */
	public Set<Integer> getRealSet() {
		return realSet;
	}

	/**
	 * @return the map from individual URIs to identifiers
	 */
	public Map<String,Integer> getIndividualMap() {
		return indMap;
	}

	/**
	 * @return the map from predicate URIs to identifiers and flags
	 */
	public Map<String,int[]> getPredicateMap() {
		return predMap;
	}

	/**
	 * @return the map from string literals to identifiers
	 */
	public Map<String,Integer> getStringMap() {
		return stringMap;
	}

	/**
	 * @return the set of axioms in the TBox
	 */
	public OWLAxiom[] getTboxAxioms() {
		return tboxAxioms;
	}

	/**
	 * @return the number of assertions in the ABox completion
	 */
	public int getNumberOfAssertions() {
		return numAssertions;
	}

}

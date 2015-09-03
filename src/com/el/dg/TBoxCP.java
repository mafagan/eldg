package com.el.dg;

import java.io.File;
import java.util.List;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Connection;
import java.sql.DriverManager;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map.Entry;


import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;

import de.tudresden.inf.lat.jcel.coreontology.axiom.GCI0Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.GCI1Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.GCI2Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.GCI3Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.NormalizedIntegerAxiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.RI1Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.RI2Axiom;
import de.tudresden.inf.lat.jcel.coreontology.axiom.RI3Axiom;
import de.tudresden.inf.lat.jcel.owlapi.main.JcelReasoner;
import de.tudresden.inf.lat.jcel.owlapi.translator.TranslationRepository;
import de.tudresden.inf.lat.jcel.reasoner.main.RuleBasedReasoner;

import utils.IntArrayComparator;
import utils.LOG;
import utils.Literal;
import utils.LogicalRule;
import utils.OWL2Rule;

public class TBoxCP {
//	final private static IRI HU_IRI = IRI.create("http://localhost/HU");
//	final private static int HU_PID = -1;
	
	final private static String ctable = "(id int not null, "
			+ "node int not null, " + "is_new tinyint null, "
			+ "primary key (id), " + "unique (node), " + "index (is_new))";
	final private static String rtable = "(id int not null, "
			+ "fnode int not null, " + "tnode int not null, "
			+ "is_new tinyint null, " + "primary key (id), "
			+ "unique (fnode,tnode), " + "unique (tnode,fnode), "
			+ "index (is_new))";
	
	final private static String ttable = "(id int not null, "
			+ "fir_node int not null, " + "sec_node int not null, " + "third_node int not null,"
			+ "is_new tinyint null, " + "primary key (id), "
			+ "unique (fir_node,sec_node,third_node), "
			+ "index (is_new))";
	
	final private static String[] MAP_BIND = {"node", "fnode", "tnode", "fonode"};
	final private static String TEMP_FILE = "temp.txt";
	final private static int MAX_PREDICATE_SHOWN = 5;
	
	final public static int FLAG_TEMPORARY = -1;
	final public static int FLAG_ONE_ARG = 0;
	final public static int FLAG_TWO_ARG = 1;
	final public static int FLAG_THREE_ARG = 2;

	/* A ⊑ B */
	final public static int SC_1 = 1;

	/* A1 ⊓ A2 ⊑ B */
	final public static int SC_2 = 2;

	/* A ⊑ ∃r.B */
	final public static int SE_1 = 3;

	/* ∃r.A ⊑ B */
	final public static int SE_2 = 4;

	/* r ⊑ s */
	final public static int SR_1 = 5;

	/* r ∘ s ⊑ t */
	final public static int SR_2 = 6;

	final public static int CR_SIZE = 8;

	final public static int CR_1 = 1;
	final public static int CR_2 = 2;
	final public static int CR_3 = 3;
	final public static int CR_4 = 4;
	final public static int CR_5 = 5;
	final public static int CR_6 = 6;
	final public static int CR_7 = 7;
	final public static int CR_8 = 8;


	/**************** Discard **************/
	final public static int FLAG_INTEGER_ROLE = 3;
	final public static int FLAG_REAL_ROLE = 4;
	final public static int FLAG_SAME_AS = 5;
	/**************************************/
	
	private OWLOntology ontology;
	private RuleBasedReasoner ruleBasedReasoner = null;
	private Set<NormalizedIntegerAxiom> normalizedIntegerAxiomSet = null;
	private Map<Integer , OWLClass> classMap = null;
	private Map<Integer, OWLObjectProperty> propMap = null;
	private Map<Integer, String> predicateMap = null;
	
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
	
	public static final String driver = "com.mysql.jdbc.Driver";
	
	private ArrayList<LogicalRule> rules;
	
	public TBoxCP(Connection connection, Set<NormalizedIntegerAxiom> norAxiomSet) throws ClassNotFoundException, SQLException, FileNotFoundException{
		dbConnection = connection;
        normalizedIntegerAxiomSet = norAxiomSet;
	}

	public void generate() throws FileNotFoundException, SQLException {
//		initPred();

//		normalize();

		storeAssertions();

		generateEntailment();

	}

	private void generateEntailment() throws FileNotFoundException, SQLException {
		int oldAssertion = 0;

		while (numAssertions>oldAssertion){
			oldAssertion = numAssertions;

			for (int i=0; i<CR_SIZE; i++)
				processRule(i);
		}
	}

	private void processRule(int ruleID) throws FileNotFoundException, SQLException{
		Statement stmt = dbConnection.createStatement(ResultSet.TYPE_FORWARD_ONLY, ResultSet.CONCUR_READ_ONLY);
		TreeSet<int[]> keySet = new TreeSet<int[]>(new IntArrayComparator());

		PrintStream out = new PrintStream(TEMP_FILE);


		ResultSet rs = stmt.executeQuery(SQLStmt.rules[ruleID]);
		while (rs.next()){
			if (rs.getInt("id") == 0){
				int[] key = new int[rs.getMetaData().getColumnCount()-1];
				for (int i=0; i<key.length; i++){
					key[i] = rs.getInt(i+1);
				}

				if (!keySet.contains(key)){
					keySet.add(key);

					out.print(++numAssertions);
					for (int i=0; i<key.length-1; i++){
						out.print("\t");
						out.print(key[i]);
					}
					out.print("\t");
					out.println(1);
				}
			}
		}
		rs.close();
		out.close();

		//TODO write back to database
		stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SQLStmt.entailmentPNum[ruleID]));
	}

	private void storeAssertions() throws SQLException, FileNotFoundException{
		//ArrayList<int[]>[] assertions = new ArrayList[predFlags.length];
		numAssertions = 0;

		Statement stmt = dbConnection.createStatement();

		for(int i=1; i<=6; i++){
			stmt.execute(String.format("drop table if exists p%d", i));
			stmt.execute(String.format("drop table if exists tp%d", i));
			if (i==SC_1 || i==SR_1) {
				stmt.execute(String.format("create table p%d%s", i, rtable));
				stmt.execute(String.format("create table tp%d%s", i, rtable));
			}else{
				stmt.execute(String.format("create table p%d%s", i, ttable));
				stmt.execute(String.format("create table tp%d%s", i, ttable));
			}
		}




		Iterator<NormalizedIntegerAxiom> norIterator = normalizedIntegerAxiomSet.iterator();
		while (norIterator.hasNext()) {
			NormalizedIntegerAxiom axiom = (NormalizedIntegerAxiom) norIterator.next();
			LOG.info(axiom.toString());
			PrintStream out = new PrintStream(TEMP_FILE);
			//System.out.println(axiom.getClass());
			if (axiom instanceof GCI0Axiom) {
				GCI0Axiom tmpAxiom = (GCI0Axiom) axiom;
				out.print(++numAssertions);
				out.print("\t");
				out.print(tmpAxiom.getSubClass());
				out.print("\t");
				out.print(tmpAxiom.getSuperClass());
				out.print("\t0\n");
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SC_1));
				stmt.execute(String.format("load data local infile '%s' into table tp%d", TEMP_FILE, SC_1));
			}else if (axiom instanceof GCI1Axiom) {
				GCI1Axiom tmpAxiom = (GCI1Axiom) axiom;
				out.print(++numAssertions);
				out.print("\t");
				out.print(tmpAxiom.getLeftSubClass());
				out.print("\t");
				out.print(tmpAxiom.getRightSubClass());
				out.print("\t");
				out.print(tmpAxiom.getSuperClass());
				out.print("\t0\n");
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SC_2));
				stmt.execute(String.format("load data local infile '%s' into table tp%d", TEMP_FILE, SC_2));

			}else if (axiom instanceof GCI2Axiom){
				GCI2Axiom tmpAxiom = (GCI2Axiom) axiom;

				out.print(++numAssertions);
				out.print("\t");
				out.print(tmpAxiom.getSubClass());
				out.print("\t");
				out.print(tmpAxiom.getPropertyInSuperClass());
				out.print("\t");
				out.print(tmpAxiom.getClassInSuperClass());
				out.print("\t0\n");
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SE_1));
				stmt.execute(String.format("load data local infile '%s' into table tp%d", TEMP_FILE, SE_1));
			}else if (axiom instanceof GCI3Axiom) {
				GCI3Axiom tmpAxiom = (GCI3Axiom) axiom;
				out.print(++numAssertions);
				out.print("\t");
				out.print(tmpAxiom.getPropertyInSubClass());
				out.print("\t");
				out.print(tmpAxiom.getClassInSubClass());
				out.print("\t");
				out.print(tmpAxiom.getSuperClass());
				out.print("\t0\n");
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SE_2));
				stmt.execute(String.format("load data local infile '%s' into table tp%d", TEMP_FILE, SE_2));
			}else if (axiom instanceof RI2Axiom){
				RI2Axiom tmpAxiom = (RI2Axiom) axiom;
				out.print(++numAssertions);
				out.print("\t");
				out.print(tmpAxiom.getSubProperty());
				out.print("\t");
				out.print(tmpAxiom.getSuperProperty());
				out.print("\t0\n");
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SR_1));
				stmt.execute(String.format("load data local infile '%s' into table tp%d", TEMP_FILE, SR_1));
			}else if (axiom instanceof RI3Axiom){
				RI3Axiom tmpAxiom = (RI3Axiom) axiom;
				out.print(++numAssertions);
				out.print("\t");
				out.print(tmpAxiom.getLeftSubProperty());
				out.print("\t");
				out.print(tmpAxiom.getRightSubProperty());
				out.print("\t");
				out.print(tmpAxiom.getSuperProperty());
				out.print("\t0\n");
				out.close();
				stmt.execute(String.format("load data local infile '%s' into table p%d", TEMP_FILE, SR_2));
				stmt.execute(String.format("load data local infile '%s' into table tp%d", TEMP_FILE, SR_2));
			}

			//Ignore RI1Axiom nominal

			if (!dbConnection.getAutoCommit())
				dbConnection.commit();

		}
		stmt.close();
		(new File(TEMP_FILE)).delete();
	}

	/* map pred and integer */
	private void initPred(){
		predicateMap = new HashMap<Integer, String>();
		predicateMap.put(SC_1, "sc_1");
		predicateMap.put(SC_2, "sc_2");
		predicateMap.put(SE_1, "se_1");
		predicateMap.put(SE_2, "se_2");
		predicateMap.put(SR_1, "sr_1");
		predicateMap.put(SR_2, "sr_2");
	}
	
	/* normalize ontology */
	private void normalize(){
		JcelReasoner reasoner = new JcelReasoner(ontology, false);
		ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();
		
		TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();
		classMap = translatorReposity.getClassMap();
		propMap = translatorReposity.getObjectPropertyMap();
		normalizedIntegerAxiomSet = ruleBasedReasoner.getNormalizedIntegerAxiomSet();
		
//		Iterator<NormalizedIntegerAxiom> iterator = normalizedIntegerAxiomSet.iterator(); 
//		Iterator<Integer> cmIterator = classMap.keySet().iterator();
//		while (cmIterator.hasNext()) {
//			Integer nAxiom = (Integer)cmIterator.next();
//			System.out.println(nAxiom + " " + classMap.get(nAxiom));
//		}
//		System.out.println(normalizedIntegerAxiomSet);
		
		Iterator<Integer> mapIterator = classMap.keySet().iterator();
		while(mapIterator.hasNext()){
			Integer numKey = (Integer) mapIterator.next();
			LOG.info(numKey + " " + classMap.get(numKey));
		}
		
		mapIterator = propMap.keySet().iterator();
		
		while (mapIterator.hasNext()) {
			Integer numKey = (Integer) mapIterator.next();
			LOG.info(numKey + " " + propMap.get(numKey));

		}
	}
	
	public void setup(List<LogicalRule> ruleList){
		//TODO create map
		rules.addAll(ruleList);
		System.out.printf("Loaded totally %d rule(s)\n", rules.size());
		
		predMap = new TreeMap<String,int[]>();
		//predMap.put(OWL2Rule.DATA_EQUAL_IRI.toString(), new int[] {OWL2Rule.DATA_EQUAL_PID, FLAG_SAME_AS});
		//predMap.put(OWL2Rule.EQUAL_IRI.toString(), new int[] {OWL2Rule.EQUAL_PID, FLAG_SAME_AS});
		predMap.put(OWL2Rule.NOT_EQUAL_IRI.toString(), new int[] {OWL2Rule.NOT_EQUAL_PID, FLAG_SAME_AS});
		predMap.put(OWL2Rule.UNIFORM_EQ_IRI.toString(), new int[] {OWL2Rule.EQUAL_PID, FLAG_SAME_AS});
		
		initPredicate();
		
		predURIs = new String[predMap.size()];
		predFlags = new int[predMap.size()];
		for (Entry<String,int[]> entry: predMap.entrySet()) {
			predURIs[entry.getValue()[0]-1] = entry.getKey();
			predFlags[entry.getValue()[0]-1] = entry.getValue()[1];
		}
		
		setupIndividuals();
		
//		Map<OWLAxiom,Integer> axiomMap = new TreeMap<OWLAxiom,Integer>();
//		for (LogicalRule rule: rules)
//		if (rule.origin != null) {
//			Integer rid = axiomMap.get(rule.origin);
//			if (rid == null) {
//				rid = new Integer(axiomMap.size()+1);
//				axiomMap.put(rule.origin, rid);
//			}
//			rule.originAID = rid.intValue();
//		}
			
	}
	
	/* Indiv means TBox_concept and TBox_role */
	private void setupIndividuals(){
		
	}
	
	/* Predicate means {sc, sr,  se}. There is no concept */
	private void initPredicate(){
		
	}
	
	public void computeCompletion() throws SQLException, FileNotFoundException{
		// rule should be safe
		
		/* It seens no necessary */
		for(LogicalRule rule : rules){
			replaceConstants(rule.head);
			replaceConstants(rule.body);
		}
	 
		for(LogicalRule rule : rules)
			composeSQL(rule);
		
		Statement stmt = dbConnection.createStatement();
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
		
		/************* HU table, not necessary *************/
		
		storeAssertions();
		
		stmt.close();
		
		// apply rules
		
		boolean[] orgTrigger = null;
		boolean[] newTrigger = new boolean[predFlags.length];
		int orgNumFacts = 0;
		while (numAssertions > orgNumFacts) {
			orgNumFacts = numAssertions;
			
		}
		
	}
	


	
	public void createCompletionTable() throws SQLException, FileNotFoundException{
		Statement stmt = dbConnection.createStatement();

		stmt.execute("drop table if exists completion");
		
		stmt.execute("create table completion(" +
				"predicate_id int not null, arg1 int not null, " + "arg2 int not null, " +
				"arg3 int not null, index (predicate_id))");
		if (!dbConnection.getAutoCommit())
			dbConnection.commit();
		
		for (int i = 0; i < predFlags.length; i++)
			if (predFlags[i] != FLAG_TEMPORARY && predFlags[i] != FLAG_SAME_AS) {
				PrintStream out = new PrintStream(TEMP_FILE);
				if (predFlags[i] == FLAG_ONE_ARG) {
					ResultSet rs = stmt.executeQuery("select node from p" + (i+1));
					while (rs.next()) {
						out.println(i+1);
						out.print("\t0\t");
						out.print(rs.getInt(1));
					}
					rs.close();
				}
				else if(predFlags[i] == FLAG_TWO_ARG){
					ResultSet rs = stmt.executeQuery("select fnode,tnode from p" + (i+1));
					while (rs.next()) {
						out.print(i+1);
						out.print('\t');
						out.print(rs.getInt(1));
						out.print('\t');
						out.println(rs.getInt(2));
					}
					rs.close();
				}else{
					ResultSet rs = stmt.executeQuery("select fnode,tnode from p" + (i+1));
					while (rs.next()) {
						out.print(i+1);
						out.print('\t');
						out.print(rs.getInt(1));
						out.print('\t');
						out.println(rs.getInt(2));
						out.print('\t');
						out.println(rs.getInt(3));
					}
					rs.close();
				}
				out.close();
				stmt.execute("load data local infile '" + TEMP_FILE + "' ignore into table completion");
				if (!dbConnection.getAutoCommit())
					dbConnection.commit();
			}
	}

	/* Discard */
	private void composeSQL(LogicalRule rule){
		StringBuffer sqlBuf = new StringBuffer();
		StringBuffer condBuf = new StringBuffer();
		// atom_index * 3 + type (node=0, fnode=1, tnode=2)
		Map<String,Integer> varBind = new HashMap<String,Integer>();
		
		for(int i = 0; i < rule.body.size(); i++){
			if (rule.body.get(i).id == OWL2Rule.NOT_EQUAL_PID) {
				//TODO it may not happen at all ...
			}else{
				
				// Handle the first term
				if (rule.body.get(i).arguments[0].startsWith("?")) { //It should be this
					Integer bind = varBind.get(rule.body.get(i).arguments[0]);
					
					if (bind != null) {
						//TODO
						
					}else {
						int v = make_bind(i, rule.body.get(i).arguments.length);
						varBind.put(rule.body.get(i).arguments[0], v);
					}
				}
				
				// Handle the second term
				if (rule.body.get(i).arguments.length > 1) {
					if (rule.body.get(i).arguments[1].startsWith("?")){ // It should be this
						Integer bind = varBind.get(rule.body.get(i).arguments[1]);
						
						if (bind != null) {
							//TODO
						}else{
							int v = make_bind(i, 2);  //TODO why?
							varBind.put(rule.body.get(i).arguments[1], v);
						}
					}
				}
				
				// Handle the third term
				if (rule.body.get(i).arguments.length > 2){
					if (rule.body.get(i).arguments[2].startsWith("?")){
						Integer bind = varBind.get(rule.body.get(i).arguments[2]);
						
						if (bind != null) {
							//TODO
						}else{
							int v = make_bind(i, 3); //TODO why?
							varBind.put(rule.body.get(i).arguments[2], v);
						}
					}
				}
				
				
			}
		}
		
		Set<Integer> binds = new HashSet<Integer>();
		for (int i = 0; i < rule.head.size(); i++)
		for (int j = 0; j < rule.head.get(i).arguments.length; j++)
			if (rule.head.get(i).arguments[j].startsWith("?")){ //It should be this
				Integer bind = varBind.get(rule.head.get(0).arguments[j]);
				if (bind == null) {
					System.out.printf("%s should appear in the body of %s%n", rule.head.get(i).arguments[j], rule);
					return;
				}else if (!binds.contains(bind)) {
					binds.add(bind);
					int v = bind.intValue();
					
					//TODO
				}
			}
	}
	
	private int make_bind(int x, int t){
		//TODO check if it is correct
		return x*4+t;
	}
	
	/* It seens no necessary */
	private void replaceConstants(List<Literal> atoms){
		for (int i = 0; i < atoms.size(); i++) {
			for (int j = 0; j < atoms.get(i).arguments.length; j++) {
				//TODO 
			}
		}
	}

	public void addRule(LogicalRule rule){
		rules.add(rule);
	}
}

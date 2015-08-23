package com.el.dg;

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
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map.Entry;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;

import utils.IntArrayComparator;
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
			+ "fnode int not null, " + "tnode int not null, " + "fonode int not null,"
			+ "is_new tinyint null, " + "primary key (id), "
			+ "unique (fnode,tnode,fonode), " + "unique (tnode,fnode), "
			+ "index (is_new))";
	
	final private static String[] MAP_BIND = {"node", "fnode", "tnode", "fonode"};
	final private static String TEMP_FILE = "temp.txt";
	final private static int MAX_PREDICATE_SHOWN = 5;
	
	final public static int FLAG_TEMPORARY = -1;
	final public static int FLAG_ONE_ARG = 0;
	final public static int FLAG_TWO_ARG = 1;
	final public static int FLAG_THREE_ARG = 2;
	
	/**************** Discard **************/
	final public static int FLAG_INTEGER_ROLE = 3;
	final public static int FLAG_REAL_ROLE = 4;
	final public static int FLAG_SAME_AS = 5;
	/**************************************/
	
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
	
	public TBoxCP(String url, String user, String pwd) throws ClassNotFoundException, SQLException{
		Class.forName(TBoxCP.driver);
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
	
	private void processRule(LogicalRule rule, boolean[] orgTrigger, boolean[] newTrigger) throws FileNotFoundException, SQLException{
		Statement stmt = dbConnection.createStatement(ResultSet.TYPE_FORWARD_ONLY, ResultSet.CONCUR_READ_ONLY);
		TreeSet<int[]> keySet = new TreeSet<int[]>(new IntArrayComparator());
		
		PrintStream out = new PrintStream(TEMP_FILE);
	}
	
	private void storeAssertions(){
		ArrayList<int[]>[] assertions = new ArrayList[predFlags.length];
		
		//TODO store all known TBOX 
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

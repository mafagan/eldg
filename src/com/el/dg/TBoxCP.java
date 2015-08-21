package com.el.dg;

import java.util.List;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Connection;
import java.sql.DriverManager;
import java.util.ArrayList;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;

import utils.LogicalRule;

public class TBoxCP {
//	final private static IRI HU_IRI = IRI.create("http://localhost/HU");
//	final private static int HU_PID = -1;
	final private static String[] MAP_BIND = {"node", "fnode", "tnode", "lnode"};
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
	
	public  void setup(){
		//TODO create map
	}
	
	public void computeCompletion(){
		
	}
	
	public void addRule(LogicalRule rule){
		rules.add(rule);
	}
}

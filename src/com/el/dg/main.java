package com.el.dg;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import org.semanticweb.owlapi.model.IRI;

import utils.Literal;
import utils.LogicalRule;

public class main {

	/**
	 * @param args
	 * @throws SQLException 
	 * @throws ClassNotFoundException 
	 */
	public static final String url = "jdbc:mysql://localhost/test";
	public static final String user = "root";
	public static final String password = "";
			
	public static void main(String[] args) throws SQLException, ClassNotFoundException {
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
		IRI likeIri = IRI.create("http://danye.me/like");
		Literal body1 = new Literal(likeIri, new String[]{"?A", "?B", "?C"});
		Literal body2 = new Literal(likeIri, new String[]{"?B", "?C", "?D"});
		Literal head = new Literal(likeIri, new String[]{"?A", "?B", "?D"});
		
		LogicalRule rule = new LogicalRule();
		rule.head.add(head);
		rule.body.add(body1);
		rule.body.add(body2);
		
		TBoxCP generator = new TBoxCP(url, user, password);
		generator.addRule(rule);
		generator.computeCompletion();
	}

}

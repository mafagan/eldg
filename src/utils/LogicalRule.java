package utils;

import java.util.ArrayList;

import org.semanticweb.owlapi.model.OWLAxiom;

public class LogicalRule {
	public ArrayList<Literal> head;
	public ArrayList<Literal> body;
	public String sql;
	public OWLAxiom origin;
	public int originAID;

	public LogicalRule() {
		head = new ArrayList<Literal>();
		body = new ArrayList<Literal>();
		sql = null;
		origin = null;
		originAID = 0;
	}

	public boolean equals(LogicalRule r) {
		if (r.head.size() != head.size() || r.body.size() != body.size())
			return false;
		for (int i = 0; i < head.size(); i++)
			if (!head.get(i).equals(r.head.get(i)))
				return false;
		for (int i = 0; i < body.size(); i++)
			if (!body.get(i).equals(r.body.get(i)))
				return false;
		return true;
	}

	public String toString() {
		StringBuffer buf = new StringBuffer();
		for (int i = 0; i < head.size(); i++) {
			if (i > 0)
				buf.append(" v ");
			buf.append(head.get(i).predicate.toString());
			buf.append("(");
			for (int j = 0; j < head.get(i).arguments.length; j++) {
				if (j > 0)
					buf.append(",");
				buf.append(head.get(i).arguments[j]);
			}
			buf.append(")");
		}
		if (body.size() > 0) {
			if (head.size() > 0)
				buf.append(" :- ");
			else
				buf.append(":- ");
			for (int i = 0; i < body.size(); i++) {
				if (i > 0)
					buf.append(",");
				buf.append(body.get(i).predicate);
				buf.append("(");
				for (int j = 0; j < body.get(i).arguments.length; j++) {
					if (j > 0)
						buf.append(",");
					buf.append(body.get(i).arguments[j]);
				}
				buf.append(")");
			}
		}
		buf.append(".");
		return buf.toString();
	}
}

package utils;

import org.semanticweb.owlapi.model.IRI;

public class Literal {
	public int id;
	public IRI predicate;
	public String[] arguments;
	public int[] values;

	public Literal(IRI predicate, String[] arguments) {
		this.id = 0;
		this.predicate = predicate;
		this.arguments = arguments;
		this.values = null;
	}

	public boolean equals(Literal l) {
		if (!predicate.equals(l.predicate) || arguments.length != l.arguments.length)
			return false;
		for (int i = 0; i < arguments.length; i++)
			if (!arguments[i].equals(l.arguments[i]))
				return false;
		return true;
	}

	public boolean equalsUsingId(Literal l) {
		if (id != l.id || arguments.length != l.arguments.length)
			return false;
		for (int i = 0; i < arguments.length; i++)
			if (!arguments[i].equals(l.arguments[i]))
				return false;
		return true;
	}

	public Literal() {
		id = 0;
		predicate = null;
		arguments = null;
		values = null;
	}
}

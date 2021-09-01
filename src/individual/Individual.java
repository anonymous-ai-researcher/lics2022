package individual;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import concepts.ConceptExpression;

public class Individual extends ConceptExpression {

	public Individual() {
		super();
	}

	public Individual(String str) {
		super(str);
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getText()).toHashCode();
	}

}

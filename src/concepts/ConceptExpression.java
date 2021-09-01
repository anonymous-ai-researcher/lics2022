package concepts;

import java.util.List;

import formula.Formula;

public class ConceptExpression extends Formula {
	
	public ConceptExpression() {
		super();
	}

	public ConceptExpression(String str) {
		super(str);
	}
	
	public ConceptExpression(Formula formula) {
		super(1);
		this.setSubFormulas(formula);
	}
			
	public ConceptExpression(Formula formula1, Formula formula2) {
		super(2);
		this.setSubFormulas(formula1, formula2);
	}
	
	public ConceptExpression(List<Formula> list) {
		super(list.size());
		this.setSubFormulas(list);
	}
	
}
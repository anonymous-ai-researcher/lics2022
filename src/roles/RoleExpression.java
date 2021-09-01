/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package roles;

import java.util.List;

import formula.Formula;

/**
 *
 * @author Yizheng
 */
public class RoleExpression extends Formula {

	public RoleExpression() {
		super();
	}

	public RoleExpression(String str) {
		super(str);
	}
	
	public RoleExpression(Formula formula) {
		super(1);
		this.setSubFormulas(formula);
	}
		
	public RoleExpression(List<Formula> list) {
		super(list.size());
		this.setSubFormulas(list);
	}

}

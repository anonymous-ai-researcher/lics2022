/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package roles;

import java.util.*;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 *
 * @author Yizheng
 */
public class AtomicRole extends RoleExpression implements Comparable<AtomicRole> {
	
	public AtomicRole() {
		super();
	}

	public AtomicRole(String str) {
		super(str);
		this.c_sig = new LinkedHashSet<>();
		this.r_sig = new LinkedHashSet<>();
		this.set_r_sig(this);
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getText()).toHashCode();
	}
	
	@Override
	public int compareTo(AtomicRole atomicRole) {
		int i = this.getText().compareTo(atomicRole.getText());
		return i;
	}

}

package checkTautology;

import concepts.AtomicConcept;
import concepts.TopConcept;
import connectives.*;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;

import java.util.*;
public class TautologyChecker {
    public TautologyChecker(){

    }
    public static boolean  isTautology(Formula formula) throws Exception{
        Formula left = formula.getSubFormulas().get(0);
        Formula right = formula.getSubFormulas().get(1);
/*
        int tag = 1;
        Formula formula1 = null;
        if(formula.toString().contains("Definer")){
            tag = 0;
            Inferencer inf = new Inferencer();
            formula1 = formula.clone();
            Set<AtomicConcept> csigs = formula.get_c_sig();
            for(AtomicConcept concept : csigs){
                if(concept.toString().contains("Definer")){
                    if(DefinerIntroducer.definer_left_map.containsValue(concept)){

                        Formula temp = DefinerIntroducer.reverse_definer_left_map.get(concept);

                        formula1 = inf.AckermannReplace(concept,formula1,temp);

                    }
                    else if(DefinerIntroducer.definer_right_map.containsValue(concept)){
                        Formula temp = DefinerIntroducer.reverse_definer_right_map.get(concept);

                        formula1 = inf.AckermannReplace(concept,formula1,temp);
                    }

                }
            }
        }

 */
        if (formula instanceof Inclusion && (left instanceof And) && left.getSubformulae().contains(right)) {
            return true;
        } else if (formula instanceof Inclusion && right instanceof TopConcept) return true;
        else if (formula instanceof Inclusion && left.equals(right)) return true;
/*
        if(tag == 0) {

            left = formula1.getSubFormulas().get(0);
            right = formula1.getSubFormulas().get(1);
            if (formula1 instanceof Inclusion && (left instanceof And) && left.getSubformulae().contains(right)) {
                return true;
            } else if (formula1 instanceof Inclusion && right instanceof TopConcept) return true;
            else if (formula1 instanceof Inclusion && left.equals(right)) return true;
            return false;
        }

 */
        return false;


    }


}

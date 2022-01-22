package inference;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.TopConcept;
import convertion.BackConverter;
import convertion.Converter;
import extraction.SubsetExtractor;
import formula.Formula;
import javafx.util.Pair;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import roles.AtomicRole;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import forgetting.saveMetrics;
import java.util.*;

public class simplifier {
    public simplifier(){

    }
    public Set<OWLLogicalAxiom> extractModule(OWLOntology onto, Set<OWLEntity> sig){
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto, ModuleType.STAR);
        Set<OWLAxiom> temp = extractor.extract(sig);
        Set<OWLLogicalAxiom> ans = new HashSet<>();
        for(OWLAxiom axiom : temp ){
            if(axiom instanceof OWLLogicalAxiom) ans.add((OWLLogicalAxiom) axiom);
        }
        return  ans;

    }
    public List<AtomicConcept> ordering(Set<AtomicConcept> c_sig, List<Formula> c_sig_list_normalised){
        List<Formula> now_c_sig_list_normalised = new ArrayList<>(c_sig_list_normalised);
        List<AtomicConcept> now = new ArrayList<>(c_sig);
        FChecker fc = new FChecker();
        Queue<Pair<Integer,AtomicConcept>> Q = new PriorityQueue<>(new queueComparator());
        List<AtomicConcept> ans = new ArrayList<>();
        SubsetExtractor se = new SubsetExtractor();
        int t = 0;
        for(AtomicConcept concept : now){
            int num = 0;
            List<Formula>pivot_list_normalised = se.getConceptSubset(concept, now_c_sig_list_normalised);
            num=fc.positive(concept,pivot_list_normalised);
            num*=fc.negative(concept,pivot_list_normalised);
            Pair<Integer,AtomicConcept> temp= new Pair<>(num,concept);
            Q.add(temp);
            System.out.println(now.size()+" "+t);
            t++;

        }
        while(!Q.isEmpty()){
            Pair<Integer,AtomicConcept> temp=Q.poll();
            System.out.println(temp.getKey());
            ans.add(temp.getValue());
        }
        return ans;

    }
    public List<AtomicRole> ordering2(Set<AtomicRole> c_sig, List<Formula> r_sig_list_normalised){
        List<Formula> now_r_sig_list_normalised = new ArrayList<>(r_sig_list_normalised);
        List<AtomicRole> now = new ArrayList<>(c_sig);
        FChecker fc = new FChecker();
        Queue<Pair<Integer,AtomicRole>> Q = new PriorityQueue<>(new queueComparator2());
        List<AtomicRole> ans = new ArrayList<>();
        SubsetExtractor se = new SubsetExtractor();
        int t = 0;
        for(AtomicRole role : now){
            int num = 0;
            List<Formula>pivot_list_normalised = se.getRoleSubset(role, now_r_sig_list_normalised);
            num=fc.positive(role,pivot_list_normalised);
            num*=fc.negative(role,pivot_list_normalised);
            Pair<Integer,AtomicRole> temp= new Pair<>(num,role);
            Q.add(temp);
            System.out.println(now.size()+" "+t);
            t++;

        }
        while(!Q.isEmpty()){
            Pair<Integer,AtomicRole> temp=Q.poll();
            System.out.println(temp.getKey());
            ans.add(temp.getValue());
        }
        return ans;
    }
    public static Set<OWLClass> visited = new HashSet<>(); //用来检查是否有循环依赖
    private Set<OWLClass> dfs(OWLClass c,Map<OWLClass,Set<OWLClass>> directTable,Map<OWLClass,Set<OWLClass>> cache)throws Exception{

       if(cache.containsKey(c)) return cache.get(c);
        Set<OWLClass> temp = new HashSet<>();
        for(OWLClass child : directTable.getOrDefault(c,new HashSet<>())){
            temp.add(child);
            Set<OWLClass> next = dfs(child,directTable,cache);
            temp.addAll(next);
        }
        cache.put(c,temp);
        return temp;
    }
    private List<Set<OWLClass>> bfs(OWLClass c,Map<OWLClass,Set<OWLClass>> directTable){
        List<Set<OWLClass>> ans = new ArrayList<>();
        Set<OWLClass> next = new HashSet<>(directTable.getOrDefault(c,new HashSet<>()));
        while(!next.isEmpty()){
            Set<OWLClass> temp = new HashSet<>();
            ans.add(next);
            for(OWLClass c2 : next){
                temp.addAll(directTable.getOrDefault(c2,new HashSet<>()));
            }
            next = temp;
        }
        return ans;
    }

    private Map<OWLClass,Set<OWLClass>> generateDirectTable(Set<OWLLogicalAxiom> axioms)throws Exception{
        BackConverter bc = new BackConverter();
        Converter ct = new Converter();
        Inferencer inf = new Inferencer();
        Map<OWLClass, Set<OWLClass>> directTable = new HashMap<>(); //表示直接依赖  比如 A in B and C， B in D 则A的直接以来是B，C
        Set<OWLClass> left = new HashSet<>();//只出现在左边的class
        Set<OWLClass> right = new HashSet<>();//只出现在右边的class
        for (OWLLogicalAxiom axiom : axioms) {
            if (axiom instanceof OWLEquivalentClassesAxiom) {
                OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
                Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
                for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
                    left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                    right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
                    break;
                }
                //记录directTable
                for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
                    if (owlSCOA.getSubClass().getClassesInSignature().size() == 1 && owlSCOA.getSubClass() instanceof OWLClass) {
                        directTable.putIfAbsent(owlSCOA.getSubClass().getClassesInSignature().iterator().next(), new HashSet<>());
                        directTable.get(owlSCOA.getSubClass().getClassesInSignature().iterator().next()).addAll(
                                owlSCOA.getSuperClass().getClassesInSignature());
                    }
                    else if(owlSCOA.getSuperClass().getClassesInSignature().size() == 1 && owlSCOA.getSuperClass() instanceof OWLClass){
                        directTable.putIfAbsent(owlSCOA.getSuperClass().getClassesInSignature().iterator().next(), new HashSet<>());
                        directTable.get(owlSCOA.getSuperClass().getClassesInSignature().iterator().next()).addAll(
                                owlSCOA.getSubClass().getClassesInSignature());
                    }
                    break;
                }
            } else if (axiom instanceof OWLSubClassOfAxiom) {
                OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
                left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
                //记录directTable
                if (owlSCOA.getSubClass().getClassesInSignature().size() == 1 && owlSCOA.getSubClass() instanceof OWLClass) {
                    directTable.putIfAbsent(owlSCOA.getSubClass().getClassesInSignature().iterator().next(), new HashSet<>());
                    directTable.get(owlSCOA.getSubClass().getClassesInSignature().iterator().next()).addAll(
                            owlSCOA.getSuperClass().getClassesInSignature());
                }
            }

        }
        return directTable;
    }

    private Map<OWLClass,Set<OWLLogicalAxiom>> generateMap(Set<OWLLogicalAxiom> axioms){
        Map<OWLClass, Set<OWLLogicalAxiom>> map = new HashMap<>();
        for(OWLLogicalAxiom axiom : axioms){
            //记录forgetting concept对应的axioms
            Set<OWLClass> temp = axiom.getClassesInSignature();
            for (OWLClass c : temp) {
                if (map.getOrDefault(c, null) == null) {
                    map.put(c, new HashSet<>());
                }
                map.get(c).add(axiom);
            }
        }
        return map;
    }
    private void testExtradfs(OWLClass c,Map<OWLClass,Set<OWLClass>> directTable ,Map<OWLClass, Set<OWLLogicalAxiom>> map,Set<OWLClass> visited)throws Exception{
        if(visited.contains(c)) {
            System.out.println("visited " + visited);
            System.out.println("map");
            for(OWLClass temp : visited){
                System.out.println(map.get(temp));
            }
            throw new Exception();
        }
        visited.add(c);
        for(OWLClass next : directTable.getOrDefault(c,new HashSet<>())){
            testExtradfs(next,directTable,map,visited);
        }
        visited.remove(c);

    }
    public void testExtra(Set<OWLLogicalAxiom> axioms,Set<OWLClass> concepts)throws Exception {
        Map<OWLClass,Set<OWLClass>> directTable = generateDirectTable(axioms);
        Map<OWLClass, Set<OWLLogicalAxiom>> map =generateMap(axioms);
        Set<OWLClass> visited = new HashSet<>();
        for(OWLClass c : concepts){
            System.out.println("concept " + c);
            testExtradfs(c,directTable,map,visited);
        }

    }

    public Map<OWLClass,Set<OWLClass>> definedConceptsRightclosure(Set<OWLLogicalAxiom> axioms)throws  Exception{
        Map<OWLClass,Set<OWLClass>> directTable = generateDirectTable(axioms);
        Map<OWLClass,Set<OWLClass>> tables = new HashMap<>();
        int i = 0;
        Map<OWLClass,Set<OWLClass>> cache = new HashMap<>();
        for(OWLClass c : directTable.keySet()){
            visited.clear();
            System.out.println("forget " + c);
            Set<OWLClass> now = dfs(c,directTable,cache);
            /*
            List<Set<OWLClass>> now2 = bfs(c,directTable);
            Set<OWLClass> temp = new HashSet<>();
            for(Set<OWLClass> set : now2)
                temp.addAll(set);
            if(!temp.containsAll(now) || !now.containsAll(temp)) throw new Exception();

             */
           /*
            Set<OWLClass> last = new HashSet<>();
            Set<OWLClass> current = new HashSet<>();
            current.add(c);
            while(!current.isEmpty()){
                last.addAll(current);
                Set<OWLClass> temp = new HashSet<>();
                for(OWLClass child : current){
                    temp.addAll(directTable.getOrDefault(child,new HashSet<>()));
                }
                for(OWLClass father : last){
                    tables.putIfAbsent(father,new HashSet<>());
                    tables.get(father).addAll(temp);
                }
                //temp.removeAll(last);
                int size =temp.size();
                System.out.println(temp);
                temp.removeAll(last);
                System.out.println(last);
                if(temp.size() != size) throw new Exception();
                current = temp;
            }

            */
            tables.put(c,now);
            System.out.println(i++ +" " + directTable.keySet().size()+" "+tables.get(c).size());
        }
        return tables;
    }

    /**
     *
     * @param axioms 等待优化的axiom
     * @param concepts concept的删除范围
     * @return 去掉涉及defined concepts的axioms 和替换based concept到的axioms的axioms集合
     * 		//优化：defined concepts指的是只出现在equiv或inclusion左边的concept names(A and B = B and C中，A和B都不是defined name 即使没有了其他的式子，对于defined concept A，如果A
     * 		// 涉及的axiom只有1个，则直接删掉涉及的axiom， 如果A涉及到的axioms有多个，就先用equiv的右边去替换inclusion中的A，再删除掉equiv
     */
    public Set<OWLLogicalAxiom> eliminateDefinedConceptsAndBasedConcepts(Set<OWLLogicalAxiom> axioms,Set<OWLClass> concepts,saveMetrics metrics)throws Exception{
        double time1 = System.currentTimeMillis();
        BackConverter bc = new BackConverter();
        Converter ct = new Converter();
        Inferencer inf = new Inferencer();
        Map<OWLClass,Set<OWLLogicalAxiom>> map = new HashMap<>();
        Set<OWLClass> left = new HashSet<>();//出现在过左边的entity
        Set<OWLClass> right = new HashSet<>();//出现在过右边的entity
        for(OWLLogicalAxiom axiom : axioms){
            if(axiom instanceof OWLEquivalentClassesAxiom){
                OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
                Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
                for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
                   // if(owlSCOA.getSubClass() instanceof OWLClass) {
                        left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                        right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
                        break;
                  //  }else if(owlSCOA.getSuperClass() instanceof OWLClass){
                  //      right.addAll(owlSCOA.getSubClass().getClassesInSignature());
                  //      left.addAll(owlSCOA.getSuperClass().getClassesInSignature());
                 //       break;
                  //  }
                }
            }else if(axiom instanceof  OWLSubClassOfAxiom){
                OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
                left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
            }
            //记录forgetting concept对应的axioms
            Set<OWLClass> temp = axiom.getClassesInSignature();
            temp.retainAll(concepts);
            for(OWLClass c : temp){
                if(map.getOrDefault(c,null) == null){
                    map.put(c,new HashSet<>());
                }
                map.get(c).add(axiom);
            }

        }

        Set<OWLClass> tempLeft = new HashSet<>(left);//副本
        int tempConceptSize = concepts.size();//副本
        //只保留要遗忘的符号的
        left.retainAll(concepts);
        int optimizeNum1 = 0,optimizeNum2 = 0, optimizeNum3 = 0,optimizeNum4 = 0;// case1 case 2 case3 和 based concept优化

        //记录被移除的axiom 目的是当同一个axiom涉及多个forgetting signature时，要把后处理的forgetting signature涉及的已经处理过的axiom给删除掉
        Set<OWLLogicalAxiom> removedAxioms = new HashSet<>();

        for(OWLClass c: left){

            Set<OWLLogicalAxiom> axiom_set_contained_defined_concept = map.get(c);
            axiom_set_contained_defined_concept.removeAll(removedAxioms);
            OWLEquivalentClassesAxiom definition_axiom = null;
            OWLClassExpression definition_of_defined_concept = null;

            int haveEquiv = 0;


            for(OWLLogicalAxiom temp : axiom_set_contained_defined_concept){
                if(temp instanceof OWLEquivalentClassesAxiom) {
                    haveEquiv = 1;
                    for(OWLSubClassOfAxiom owlSCOA :((OWLEquivalentClassesAxiom)temp).asOWLSubClassOfAxioms()){
                        if(owlSCOA.getSubClass().equals(c)){

                            definition_axiom = (OWLEquivalentClassesAxiom)temp;
                            definition_of_defined_concept = owlSCOA.getSuperClass();

                        }else if(owlSCOA.getSuperClass().equals(c)){
                            definition_axiom =  (OWLEquivalentClassesAxiom)temp;
                            definition_of_defined_concept = owlSCOA.getSubClass();
                            //throw new Exception();
                        }
                        break;
                    }
                }
            }

            if(haveEquiv == 1 && definition_axiom == null){//有A and B = C and D的形式 要全部保留
                /*
                if(axiom_set_contained_defined_concept.size()  == 1) {
                    optimizeNum1++;
                    concepts.remove(c);
                    axioms.removeAll(axiom_set_contained_defined_concept);
                    removedAxioms.addAll(axiom_set_contained_defined_concept);
                }

                 */

            }else if(haveEquiv == 0 && !right.contains(c)){//只有 A in C 或者 A and B in C这样的
                optimizeNum2++;
                concepts.remove(c);
                axioms.removeAll(axiom_set_contained_defined_concept);
                removedAxioms.addAll(axiom_set_contained_defined_concept);

            } else if(haveEquiv == 1 && definition_axiom != null){// 有A的定义式的情况，拿A的右边的表达式去替换所有出现A的位置的东西
                if(axiom_set_contained_defined_concept.size()  == 1) optimizeNum1++;
                else optimizeNum3++;
                concepts.remove(c);
                axioms.removeAll(axiom_set_contained_defined_concept);
                removedAxioms.addAll(axiom_set_contained_defined_concept);
                axiom_set_contained_defined_concept.remove(definition_axiom);
                List<Formula> formulas = ct.AxiomsConverter(axiom_set_contained_defined_concept);
                Formula definition = ct.ClassExpressionConverter(definition_of_defined_concept);
                List<Formula> ans = new ArrayList<>();
                if(definition != null) {
                    for (Formula f : formulas) {
                        ans.add(inf.AckermannReplace(ct.getConceptfromClass(c), f, definition));
                    }
                }
                Set<OWLAxiom> replaced_axioms = bc.toOWLAxioms(ans);
                for(OWLAxiom axiom : replaced_axioms){
                    Set<OWLClass> classes = axiom.getClassesInSignature();
                    classes.retainAll(concepts);
                    for(OWLClass c1 : classes){
                        if(map.getOrDefault(c1,null) == null){
                            map.put(c1,new HashSet<>());
                        }
                        map.get(c1).add((OWLLogicalAxiom)axiom);
                    }
                    if(axiom instanceof OWLSubClassOfAxiom){
                        right.addAll(((OWLSubClassOfAxiom)axiom).getSuperClass().getClassesInSignature());
                        tempLeft.addAll(((OWLSubClassOfAxiom)axiom).getSubClass().getClassesInSignature());//todo add
                    }else throw  new Exception();/*
                    else if(axiom instanceof OWLEquivalentClassesAxiom){
                        OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
                        Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
                        int tag = 1;
                        for(OWLSubClassOfAxiom axiom1 : owlSubClassOfAxioms){
                            if(axiom1.getSubClass() instanceof OWLClass){
                                tag = 0;
                                right.addAll(axiom1.getSuperClass().getClassesInSignature());
                            }else if(axiom1.getSuperClass() instanceof OWLClass){
                                tag = 0;
                                right.addAll(axiom1.getSubClass().getClassesInSignature());
                            }
                            break;
                        }
                        if(tag == 1){
                            right.addAll(axiom.getClassesInSignature());
                        }
                    }
                    */
                    //else throw new Exception();
                    axioms.add((OWLLogicalAxiom)axiom);
                }
            }
        }

        System.out.println("before remove defined concept size "+ tempConceptSize +" after "+concepts.size());

        //计算base concept
        tempConceptSize = concepts.size();
        right.removeAll(tempLeft);//此时right和left不相交，表示只出现在右边的class
        right.retainAll(concepts);
        for(OWLClass c : right){
            AtomicConcept atomicConcept = ct.getConceptfromClass(c);
            Set<OWLLogicalAxiom> axiom_set_contained_based_concept = map.get(c);
            axiom_set_contained_based_concept.removeAll(removedAxioms);
            int tag = 0;
            for(OWLLogicalAxiom axiom : axiom_set_contained_based_concept){
                if(axiom instanceof OWLEquivalentClassesAxiom) tag = 1;
            }
            if(tag == 0){
                optimizeNum4++;
               // concepts.remove(c); // todo
                axioms.removeAll(axiom_set_contained_based_concept);
                removedAxioms.addAll(axiom_set_contained_based_concept);

                List<Formula> formulas = ct.AxiomsConverter(axiom_set_contained_based_concept);
                Formula definition = TopConcept.getInstance();
                List<Formula> ans = new ArrayList<>();
                for (Formula f : formulas) {
                    ans.add(inf.AckermannReplace(atomicConcept, f, definition));
                }

                Set<OWLAxiom> replaced_axioms = bc.toOWLAxioms(ans);
                for(OWLAxiom axiom : replaced_axioms){
                    Set<OWLClass> classes = axiom.getClassesInSignature();
                    classes.retainAll(concepts);
                    for(OWLClass c1 : classes){
                        if(map.getOrDefault(c1,null) == null){
                            map.put(c1,new HashSet<>());
                        }
                        map.get(c1).add((OWLLogicalAxiom)axiom);
                    }
                    axioms.add((OWLLogicalAxiom)axiom);
                }


            }
        }
        double time2 = System.currentTimeMillis();
        metrics.optimizeNum1 = optimizeNum1;
        metrics.optimizeNum2 = optimizeNum2;
        metrics.optimizeNum3 = optimizeNum3;
        metrics.optimizeNum4 = optimizeNum4;
        metrics.optimizeTime = (time2-time1);

        System.out.println("before replaced based concept size "+ tempConceptSize +" after "+concepts.size());
        //System.out.println(optimizeNum1+" "+optimizeNum2+" "+optimizeNum3+" "+optimizeNum4 + " "+concepts.size());
        return axioms;
    }


}
class queueComparator implements  Comparator<Pair<Integer,AtomicConcept>>{
    public int compare(Pair<Integer,AtomicConcept> e1, Pair<Integer,AtomicConcept> e2) {
        return e1.getKey() - e2.getKey();//升序
        //return e2.getKey() - e1.getKey();//降序

    }
}
class queueComparator2 implements  Comparator<Pair<Integer,AtomicRole>>{
    public int compare(Pair<Integer,AtomicRole> e1, Pair<Integer,AtomicRole> e2) {
        return e1.getKey() - e2.getKey();//升序
        //return e2.getKey() - e1.getKey();//降序

    }
}
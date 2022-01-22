package Test;
import java.io.*;
import java.lang.ref.Reference;
import java.util.*;

import checkTautology.TautologyChecker;
import checkexistence.EChecker;
import checkfrequency.FChecker;
import com.google.common.collect.Sets;
import concepts.AtomicConcept;
import concepts.TopConcept;
import convertion.BackConverter;
import convertion.Converter;
import forgetting.*;
import formula.Formula;
import inference.Inferencer;
import inference.simplifier;
import javafx.fxml.LoadException;
import org.apache.commons.lang3.builder.ToStringExclude;
import org.checkerframework.checker.units.qual.A;
import org.checkerframework.checker.units.qual.C;
import org.junit.Test;
import org.semanticweb.HermiT.*;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.NullProgressMonitor;
import roles.AtomicRole;
import sun.misc.FormattedFloatingDecimal;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import elk.*;
import connectives.*;
import com.google.common.collect.*;
import java.util.concurrent.*;
import uk.ac.man.cs.lethe.forgetting.AlchTBoxForgetter;

import javax.swing.text.html.parser.Entity;

public class TestForgetting {

    static int a = 3;
    public static ArrayList<String> getFileName(String path){
        ArrayList<String> listFileName = new ArrayList<>();
        File file =new File(path);
        String[] names= file.list();
        for(String name : names){
            listFileName.add(path+name);
        }
        return listFileName;
    }
    public static void saveUI(Set<OWLAxiom> ui, String path)throws Exception{
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        saveOntology(manager,ui,path);
        /*
        OWLOntology now = manager.createOntology(ui);
        OutputStream ops = new FileOutputStream(new File(path));
        saveOntology(manager2, myForgettingUI, dictPath + "uiPrototype.owl");

        manager.saveOntology(now, ops);

         */
    }
    public static void saveOntology(OWLOntologyManager manager2,OWLOntology onto,String path)throws Exception{
        OWLOntology myForgettingUIsave = manager2.createOntology();
        for(OWLLogicalAxiom axiom : onto.getLogicalAxioms())
            manager2.applyChange(new AddAxiom(myForgettingUIsave, axiom));
        manager2.saveOntology(myForgettingUIsave,new FileOutputStream(new File(path)));
    }

    public static void saveOntology(OWLOntologyManager manager2,Set<OWLAxiom> axioms,String path)throws Exception{
        OWLOntology myForgettingUIsave = manager2.createOntology();
        for(OWLAxiom axiom : axioms)
            manager2.applyChange(new AddAxiom(myForgettingUIsave, axiom));
        manager2.saveOntology(myForgettingUIsave,new FileOutputStream(new File(path)));
    }

    public static List<OWLObjectProperty> getSubStringByRadom1(List<OWLObjectProperty> list, int count){
        List backList = null;
        backList = new ArrayList<OWLObjectProperty>();
        Random random = new Random();
        Set<Integer> hasVisited = new HashSet<>();

        int backSum = 0;
        if (list.size() >= count) {
            backSum = count;
        }else {
            backSum = list.size();
        }
        for (int i = 0; i < backSum; i++) {
//			随机数的范围为0-list.size()-1
            int target = random.nextInt(list.size());
            if(hasVisited.contains(target)){
                i--;
                continue;
            }
            hasVisited.add(target);
            backList.add(list.get(target));
        }
        return backList;
    }
    public static List<OWLClass> getSubStringByRadom2(List<OWLClass> list, int count){
        List backList = null;
        backList = new ArrayList<OWLClass>();
        Random random = new Random();
        Set<Integer> hasVisited = new HashSet<>();
        int backSum = 0;
        if (list.size() >= count) {
            backSum = count;
        }else {
            backSum = list.size();
        }
        for (int i = 0; i < backSum; i++) {
//			随机数的 ≤./范围为0-list.size()-1
            int target = random.nextInt(list.size());
            if(hasVisited.contains(target)){
                i--;
                continue;
            }
            hasVisited.add(target);
            backList.add(list.get(target));
        }
        //System.out.println(hasVisited);
        return backList;
    }
    public static int afterForgettingAxiomsSize = 0;
    public static int beforeForgettingAxiomsSize = 0;
    public static OWLOntology onto = null;
    public static double time = 0;
    public static int isExtra = 0;
    public static  int hasFinished = 0;
    public static double mem = 0;
    public static  List<Double> depthMeanMedian = new ArrayList<>();
    public static int success = 0;
    public static  int witness_explicit_onto = 0;
    public static  int witness_implicit_onto  = 0;
    public static String nowLog = null;
    public static OWLOntology resultOWLOntology;
    public static int isExtra(OWLOntology resultontology){
        Set<OWLClass> conceptn = resultontology.getClassesInSignature();
        for (OWLClass concept : conceptn) {
            if (concept.getIRI().getShortForm().startsWith("_D")){
                System.out.println(concept.getIRI().getShortForm());
                return 1;
            }
        }
        return 0;
    }
    public static Map<AtomicConcept,Integer> Depth(List<Formula> formulas){
        int depth = 0;
        Map<AtomicConcept,Integer> depthMap = new HashMap<>();
        for(Formula formula : formulas){
            Depth(formula,0,depthMap);
        }
        return depthMap;

    }
    public static  void Depth(Formula formula,int nowdepth, Map<AtomicConcept,Integer> depthMap){
        if(formula instanceof AtomicConcept){
            AtomicConcept concept = (AtomicConcept) formula;
            int now = depthMap.getOrDefault(concept,1);
            now = Math.max(now,nowdepth);
            depthMap.put(concept,now);
            return;
        }
        if(formula instanceof Equivalence || formula instanceof Inclusion){
            Depth(formula.getSubFormulas().get(0),nowdepth,depthMap);
            Depth(formula.getSubFormulas().get(1),nowdepth,depthMap);
        }
        if(formula instanceof Exists){
            Depth(formula.getSubFormulas().get(1),nowdepth+1,depthMap);
        }
        if(formula instanceof And){
            for(Formula temp : ((And)formula).getSubformulae()){
                Depth(temp,nowdepth,depthMap);
            }
        }
    }
    public static  List<Double> getDepthMeanMedian(List<Formula>beginFormulalist, Set<OWLClass>conceptSet){
        Map<AtomicConcept,Integer> depthMap = Depth(beginFormulalist);
        List<Integer> depths = new ArrayList<>();
        Converter ct = new Converter();
        int sum = 0;
        for(OWLClass c : conceptSet){
            AtomicConcept concept =  ct.getConceptfromClass(c);
            int temp = depthMap.getOrDefault(concept,0);
            depths.add(temp);
            sum += temp;
        }
        Collections.sort(depths);
        List<Double> ans = new ArrayList<>();
        double depthMean = 0, depthMedian = 0;
        if(conceptSet.size() != 0){
            depthMean = sum*1.0/conceptSet.size();
            depthMedian = depths.get(depths.size()/2);
            ans.add(depthMean);
            ans.add(depthMedian);
            ans.add(Collections.max(depths)*1.0);
        }else{
            ans.add(0.0);
            ans.add(0.0);
            ans.add(0.0);
        }

        return ans;
    }
    public static List<OWLOntology> test3(String dictPath,String nameonto1,String nameonto2)throws Exception {
        String filelog = "logAAAI22rebuttal2" + ".txt";
        ArrayList<String> hasRecord = readFile.readFile(dictPath + filelog);

        String title = "fileName_O1,fileName_O2,LogicalAxiomsSize_O1,LogicalAxiomsSize_O2,RolesSize_O1,RolesSize_O2,ConceptsSize_O1,ConceptsSize_O2," +
                "GCISize_O1,GCISize_O2,GCIRolesSize_O1,GCIRolesSize_O2,GCIConceptSize_O1,GCIConceptSize_O2,newLogicalRoleSize,newLogicalConceptSize,newLogicalRoleSizeOccuredInGCI,newLogicalConceptSizeOccuredInGCI,time," +
                "memory,timeOut,MemoryOut," + "isSuccess,isExtra,UI_size,explicit_witness,implicit_witness\n";
        // writeFile.writeFile(dictPath+filelog,title);
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        ArrayList<String> now = getFileName(dictPath);
        List<OWLOntology> ans = new ArrayList<>();
        for (String path : now) {
            for (String path2 : now) {
                if (path.equals(path2)) continue;
                int hasRead = 0;
                for (String temp : hasRecord) {
                    if (temp.contains(path + "," + path2)) {
                        hasRead = 1;
                        break;
                    }
                }

                //if(path.contains("202001")) continue;
                if (!(path.contains(nameonto1) && path2.contains(nameonto2))) continue;

                if (hasRead == 1) continue;
                if (!path.contains(".owl") || !path2.contains(".owl")) continue;
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                String pathuiNCIT = dictPath + path.substring(path.length() - 9, path.length() - 4) + path2.substring(path2.length() - 9, path2.length() - 4) + "AAAI22rebuttal.owl";
                System.out.println(pathuiNCIT);
                System.out.println(path);
                System.out.println(path2);

                OWLOntology onto1 = manager1.loadOntologyFromOntologyDocument(new File(path));
                System.out.println("onto1 load1");
                // 统计基本的信息
                int logicalsize1 = onto1.getLogicalAxioms().size();
                int rolesize1 = onto1.getObjectPropertiesInSignature().size();
                int conceptsize1 = onto1.getClassesInSignature().size();
                int GCIsize1 = onto1.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs1 = onto1.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles1 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts1 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs1) {
                    GCIconcepts1.addAll(axiom.getClassesInSignature());
                    GCIroles1.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize1 = GCIroles1.size();
                int GCIconceptsize1 = GCIconcepts1.size();


                OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
                OWLOntology onto2 = manager2.loadOntologyFromOntologyDocument(new File(path2));
                System.out.println("onto2 load1");
                // 统计基本的信息
                int logicalsize2 = onto2.getLogicalAxioms().size();
                int rolesize2 = onto2.getObjectPropertiesInSignature().size();
                int conceptsize2 = onto2.getClassesInSignature().size();
                int GCIsize2 = onto2.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs2 = onto2.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles2 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts2 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs2) {
                    GCIconcepts2.addAll(axiom.getClassesInSignature());
                    GCIroles2.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize2 = GCIroles2.size();
                int GCIconceptsize2 = GCIconcepts2.size();


                //data

                Set<OWLClass> concepts1 = onto1.getClassesInSignature();
                Set<OWLObjectProperty> roles1 = onto1.getObjectPropertiesInSignature();

                Set<OWLClass> concepts2 = onto2.getClassesInSignature();
                Set<OWLObjectProperty> roles2 = onto2.getObjectPropertiesInSignature();

                //diff data

                Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(concepts2, concepts1));
                Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(roles2, roles1));
                Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
                Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);
                Set<OWLEntity> forgettingSignatures = new HashSet<>();
                forgettingSignatures.addAll(r_sig);
                forgettingSignatures.addAll(c_sig);

                String log = path + "," + path2 + "," + logicalsize1 + "," + logicalsize2 + "," + rolesize1 + "," + rolesize2 + "," +
                        conceptsize1 + "," + conceptsize2 + "," + GCIsize1 + "," + GCIsize2 + "," + GCIrolesize1 + "," + GCIrolesize2 + "," +
                        GCIconceptsize1 + "," + GCIconceptsize2 + "," + Sets.difference(roles2, roles1).size() + "," + Sets.difference(concepts2, concepts1).size() + "," +
                        Sets.intersection(GCIroles2, Sets.difference(roles2, roles1)).size() + "," + Sets.intersection(GCIconcepts2, Sets.difference(concepts2, concepts1)).size();

                System.out.println("gci " + GCIsize2);
                nowLog = log;
                System.out.println(nowLog);
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                Forgetter fg = new Forgetter();
                isExtra = 0;
                success = 1;
                witness_explicit_onto = 0;
                witness_implicit_onto = 0;
                elkEntailment.hasChecked_OnO2 = new HashMap<>();
                AtomicConcept.setDefiner_index(1);
                SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto2, ModuleType.STAR);
                Set<OWLAxiom> moduleOnto_2OnCommonSig = extractor.extract(Sets.difference(onto2.getSignature(), forgettingSignatures));
                Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
                for (OWLAxiom axiom : moduleOnto_2OnCommonSig) {
                    if (axiom instanceof OWLLogicalAxiom) {
                        moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                    }
                }
                System.out.println(moduleOnto_2OnCommonSig_logical.size() + " " + moduleOnto_2OnCommonSig.size());
                System.out.println("module finished");
                List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);
                try {
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    long time1 = System.currentTimeMillis();
                    System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                            + role_set.size() + "] role names from [" + moduleOnto_2OnCommonSig_logical.size() + "] normalized axioms");
                    List<Formula> ui = fg.Forgetting(r_sig, c_sig, onto2,new saveMetrics());//todo

                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                   // elkEntailment.check(onto2, ui);
                    time += (time2 - time1);
                    mem += (mem1 - mem2);
                    Set<OWLAxiom> uniform_interpolant = bc.toOWLAxioms(ui);
                    saveUI(uniform_interpolant, pathuiNCIT);
                    ans.add(onto1);
                    ans.add(onto2);
                    ans.add(bc.toOWLOntology(ui));
                    afterForgettingAxiomsSize = uniform_interpolant.size();


                } catch (OutOfMemoryError e) {
                    nowLog = nowLog + ",0,0,0,1,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("outofmemory");
                    e.printStackTrace();
                    success = 0;
                } catch (StackOverflowError e) {
                    nowLog = nowLog + ",0,0,0,2,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("stackoverflow");
                    success = 0;
                }


                if (success == 1 && isExtra == 0) {
                    nowLog = nowLog + "," + time + "," + mem / 1024 / 1024 + ",0,0,1,0," + afterForgettingAxiomsSize + ",";
                    writeFile.writeFile(dictPath + filelog, nowLog);


                }


                if (success == 1 && isExtra != 0) {
                    nowLog = nowLog + ",0,0,0,0,0," + isExtra + ",0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                }

            }

        }
        return ans;
    }
    public static OWLOntology LetheForgetting(String dictPath,String filelog,String log,Set<OWLEntity> symbols,OWLOntology onto) throws Exception{

        /*
        final ExecutorService exec = Executors.newSingleThreadExecutor();
        AlchTBoxForgetter LetheForgetter = new AlchTBoxForgetter();
        Callable<Integer> task = new Callable<Integer>() {
            @Override
            public Integer call() throws Exception {
                try {
                    isExtra = 0;
                    success = 1;
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);


                    long time1 = System.currentTimeMillis();
                    resultOWLOntology = LetheForgetter.forget(onto,symbols);
                    isExtra = isExtra(resultOWLOntology);
                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    //elkEntailment.check(onto,resultOWLOntology,symbols);
                    if(success == 1 && isExtra == 0){

                        List<Formula> ui = new Converter().OntologyConverter(resultOWLOntology);
                        System.out.println(resultOWLOntology.getLogicalAxiomCount());
                        afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui),new HashSet<>(beginFormulalist)).size();
                        beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist),new HashSet<>(ui)).size();
                        System.out.println(afterForgettingAxiomsSize+" "+beforeForgettingAxiomsSize);

                        time = (time2 - time1);
                        mem = (mem1-mem2);
                    }

                } catch (OutOfMemoryError e){
                    writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,1,0,0,0,0\n");
                    System.err.println("outofmemory");
                    success = 0;
                }

                catch (StackOverflowError e){
                    writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,1,0,0,0,0\n");
                    System.err.println("stackoverflow");
                    Thread.currentThread().interrupt();

                    success = 0;
                }catch (Exception e){

                    System.err.println(e+" runtimeerror");
                    writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,2,0,0,0,0\n");
                    Thread.currentThread().interrupt();
                    success = 0;
                }catch (Error e){
                    System.err.println(e+" runtimeerror");
                    writeFile.writeFile(dictPath+filelog,"1,"+log  +",0,0,0,3,0,0,0,0\n");
                    Thread.currentThread().interrupt();

                    success = 0;
                }
                return 1;
            }
        };
        Future<Integer> future = exec.submit(task);
        try{
            int t = future.get(1000 * 200,TimeUnit.MILLISECONDS);
        }
        catch (TimeoutException e){
            writeFile.writeFile(dictPath+filelog,"1,"+log+",0,0,1,0,0,0,0,0\n");
            success = 0;
        }

        if(success == 1 && isExtra == 0 ){

            writeFile.writeFile(dictPath+filelog,"1,"+log+","+time*1.0+","+mem/1024/1024+",0,0,1,0,"+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize +"\n");

        }
        if(success == 1 && isExtra != 0){
            writeFile.writeFile(dictPath+filelog,"1,"+log+",0,0,0,0,0,1,0,0\n");

        }
        future.cancel(true);
        exec.shutdownNow();
                return resultOWLOntology;

        */
        Thread thread = new Thread(new Runnable() {
            @Override
            public void run() {
                AlchTBoxForgetter LetheForgetter = new AlchTBoxForgetter();
                isExtra = 0;
                success = 1;
                hasFinished = 0;
                System.gc();
                Runtime r = Runtime.getRuntime();
                long mem1 = r.freeMemory();
                List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);


                long time1 = System.currentTimeMillis();
                resultOWLOntology = LetheForgetter.forget(onto, symbols);
                isExtra = isExtra(resultOWLOntology);
                long time2 = System.currentTimeMillis();
                long mem2 = r.freeMemory();
                //elkEntailment.check(onto,resultOWLOntology,symbols);
                if (success == 1 && isExtra == 0) {

                    List<Formula> ui = new Converter().OntologyConverter(resultOWLOntology);
                    System.out.println(resultOWLOntology.getLogicalAxiomCount());
                    afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui), new HashSet<>(beginFormulalist)).size();
                    beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist), new HashSet<>(ui)).size();
                    System.out.println(afterForgettingAxiomsSize + " " + beforeForgettingAxiomsSize);

                    time = (time2 - time1);
                    mem = (mem1 - mem2);
                }
                hasFinished = 1;
            }

        });
        thread.start();
        thread.join(1000 * 250);
        if(hasFinished == 0){
            writeFile.writeFile(dictPath+filelog,"1,"+log+",0,0,1,0,0,0,0,0\n");
            success = 0;
        }else {
            if (success == 1 && isExtra == 0) {

                writeFile.writeFile(dictPath + filelog, "1," + log + "," + time * 1.0 + "," + mem / 1024 / 1024 + ",0,0,1,0," + afterForgettingAxiomsSize + "," + beforeForgettingAxiomsSize + "\n");

            }
            if (success == 1 && isExtra != 0) {
                writeFile.writeFile(dictPath + filelog, "1," + log + ",0,0,0,0,0,1,0,0\n");

            }
        }
        thread.stop();
        hasFinished = 0;

        return resultOWLOntology;

    }

    public static OWLOntology LastForgetting(String dictPath,String filelog,String log, Set<OWLObjectProperty> roleSet, Set<OWLClass> conceptSet,OWLOntology onto) throws  Exception{
        final ExecutorService exec = Executors.newSingleThreadExecutor();
        Converter ct = new Converter();
        Callable<Integer> task = new Callable<Integer>() {
            @Override
            public Integer call() throws Exception {
                try {
                    isExtra = 0;
                    success = 1;
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);
                    // depthMeanMedian = getDepthMeanMedian(beginFormulalist,conceptSet);

                    long time1 = System.currentTimeMillis();
                    List<Formula> ui = new Forgetter().ForgettingOldVersion(roleSet, conceptSet, onto);
                    if (ui == null) {
                        success = 2;
                        return 1;
                    }
                    resultOWLOntology = new BackConverter().toOWLOntology(ui);
                    long time2 = System.currentTimeMillis();

                    long mem2 = r.freeMemory();
                    if (success == 1 && isExtra == 0) {
                        afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui), new HashSet<>(beginFormulalist)).size();
                        beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist), new HashSet<>(ui)).size();
                        time = (time2 - time1);
                        mem = (mem1 - mem2);
                        //elkEntailment.check(onto,ui,ct.getRolesfromObjectProperties(roleSet),ct.getConceptsfromClasses(conceptSet));

                    }
                }catch (InterruptedException e){
                    Thread.currentThread().interrupt();

                    System.out.println("Thread was interrupted, Failed to complete operation");


                }


                return 1;
            }
        };
        Future<Integer> future = exec.submit(task);
        try{
            int t = future.get(1000 * 160,TimeUnit.MILLISECONDS);
        }
        catch (TimeoutException e){
            writeFile.writeFile(dictPath+filelog,"2,"+log+",0,0,1,0,0,0,0,0,0 "+"\n");

            success = 0;
        }

        if(success == 1 && isExtra == 0 ){
            writeFile.writeFile(dictPath+filelog,"2,"+log+","+time*1.0+","+mem/1024/1024+",0,0,1,0,"+afterForgettingAxiomsSize+","+
                    beforeForgettingAxiomsSize+","+AtomicConcept.getDefiner_index()+"\n");
        }
        if(success == 1 && isExtra != 0){
            writeFile.writeFile(dictPath+filelog,"2,"+log+",0,0,0,0,0,1,0,0,0 "+"\n");
        }
        if(success == 2){//reasoner has something worong;
            writeFile.writeFile(dictPath+filelog,"2,"+log+",0,0,0,0,2,0,0,0,0 "+"\n");

        }
        future.cancel(true);
        exec.shutdownNow();

        return resultOWLOntology;
    }

    public static OWLOntology MyForgetting(String dictPath,String filelog,String log, Set<OWLObjectProperty> roleSet, Set<OWLClass> conceptSet,OWLOntology onto) throws  Exception{
        /*
        final ExecutorService exec = Executors.newSingleThreadExecutor();

        Callable<Integer> task = new Callable<Integer>() {
            @Override
            public Integer call() throws Exception {
                try {
                    isExtra = 0;
                    success = 1;
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);
                    depthMeanMedian = getDepthMeanMedian(beginFormulalist, conceptSet);

                    long time1 = System.currentTimeMillis();

                    List<Formula> ui = new Forgetter().Forgetting(roleSet, conceptSet, onto, metrics);
                    if (ui == null) {
                        success = 2;
                        return 1;
                    }
                    resultOWLOntology = new BackConverter().toOWLOntology(ui);
                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    if (success == 1 && isExtra == 0) {
                        afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui), new HashSet<>(beginFormulalist)).size();
                        beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist), new HashSet<>(ui)).size();
                        time = (time2 - time1);
                        mem = (mem1 - mem2);
                        // elkEntailment.check(onto,ui,ct.getRolesfromObjectProperties(roleSet),ct.getConceptsfromClasses(conceptSet));

                    }
                }catch (InterruptedException e){

                        Thread.currentThread().interrupt();

                        System.out.println("Thread was interrupted, Failed to complete operation");



                }
                return 1;
            }
        };
        Future<Integer> future = exec.submit(task);
        try{
            future.get(1000 * 160,TimeUnit.MILLISECONDS);
        }
        catch (TimeoutException e){
            success = 0;
            writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,1,0,0,0,0,0,0 "+metrics.returnMetrics()+"\n");
        }

        if(success == 1 && isExtra == 0 ){
            metrics.success = 1;
            metrics.isExtra = 0;
            writeFile.writeFile(dictPath+filelog,"0,"+log+","+time*1.0+","+mem/1024/1024+",0,0,1,0,"+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize+","
                    +AtomicConcept.getDefiner_index()+","+metrics.returnMetrics()+","+depthMeanMedian.get(0)+","+depthMeanMedian.get(1)+","+depthMeanMedian.get(2)+"\n");

        }
        if(success == 1 && isExtra != 0){
            metrics.isExtra = 1;
            metrics.success = 0;
            writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,0,0,0,1,0,0,0,"+metrics.returnMetrics()+"\n");

        }
        if(success == 2){//reasoner has something worong;
            writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,0,0,2,0,0,0,0,"+metrics.returnMetrics()+"\n");

        }

        future.cancel(true);
        exec.shutdownNow();

        return resultOWLOntology;

         */
        saveMetrics metrics = new saveMetrics();
        Converter ct = new Converter();
        Thread thread = new Thread(new Runnable() {
            @Override
            public void run() {
                isExtra = 0;
                success = 1;
                hasFinished = 0;
                System.gc();
                Runtime r = Runtime.getRuntime();
                long mem1 = r.freeMemory();
                List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);
                depthMeanMedian = getDepthMeanMedian(beginFormulalist, conceptSet);

                long time1 = System.currentTimeMillis();
                List<Formula> ui = null;
                try{
                    ui = new Forgetter().Forgetting(roleSet, conceptSet, onto, metrics);
                }catch (Exception e){

                }
                if (ui == null) {
                    success = 2;
                }
                try {
                    resultOWLOntology = new BackConverter().toOWLOntology(ui);
                } catch (Exception e) {

                }

                long time2 = System.currentTimeMillis();
                long mem2 = r.freeMemory();
                if (success == 1 && isExtra == 0) {
                    afterForgettingAxiomsSize = Sets.difference(new HashSet<>(ui), new HashSet<>(beginFormulalist)).size();
                    beforeForgettingAxiomsSize = Sets.difference(new HashSet<>(beginFormulalist), new HashSet<>(ui)).size();
                    time = (time2 - time1);
                    mem = (mem1 - mem2);
                    // elkEntailment.check(onto,ui,ct.getRolesfromObjectProperties(roleSet),ct.getConceptsfromClasses(conceptSet));

                }
                hasFinished = 1;
            }
        });
        thread.start();
        thread.join(1000 * 180);
        if(hasFinished == 0){
            success = 0;
            writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,1,0,0,0,0,0,0 "+metrics.returnMetrics()+"\n");

        }
        if(success == 1 && isExtra == 0 ){
            metrics.success = 1;
            metrics.isExtra = 0;
            writeFile.writeFile(dictPath+filelog,"0,"+log+","+time*1.0+","+mem/1024/1024+",0,0,1,0,"+afterForgettingAxiomsSize+","+beforeForgettingAxiomsSize+","
                    +AtomicConcept.getDefiner_index()+","+metrics.returnMetrics()+","+depthMeanMedian.get(0)+","+depthMeanMedian.get(1)+","+depthMeanMedian.get(2)+"\n");

        }
        if(success == 1 && isExtra != 0){
            metrics.isExtra = 1;
            metrics.success = 0;
            writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,0,0,0,1,0,0,0,"+metrics.returnMetrics()+"\n");

        }
        if(success == 2){//reasoner has something worong;
            writeFile.writeFile(dictPath+filelog,"0,"+log+",0,0,0,0,2,0,0,0,0,"+metrics.returnMetrics()+"\n");

        }
        thread.stop();
        hasFinished = 0;

        return resultOWLOntology;
    }

    // return is the number of witness
    public static int checkWitnessAndSave(OWLOntologyManager manager, OWLOntology onto1, OWLOntology V, String uiSavePath)throws Exception{
        int number = 0;
        OWLOntology witness = manager.createOntology();
        OWLReasoner reasoner = null;
        try {
              reasoner = new Reasoner.ReasonerFactory().createReasoner(onto);


        }catch (Exception e){
            System.err.println("HERMIT error");
            return -1;
        }
        Set<OWLLogicalAxiom> now = V.getLogicalAxioms();
        now.removeAll(onto1.getLogicalAxioms());
        int i = 0;
        try {
            for (OWLLogicalAxiom axiom : now) {
                if (!reasoner.isEntailed(axiom)) {
                    number++;
                    manager.applyChange(new AddAxiom(witness, axiom));
                }
                System.out.println("check " + i++ + " " + now.size());
            }
        }catch (Exception e){
            System.err.println("entail error");
            reasoner.dispose();
            return -3;
        }
        catch (Error e){
            System.err.println("Java heap space");
            reasoner.dispose();
            return -4;
        }
        manager.saveOntology(witness, new FileOutputStream(new File(uiSavePath)));
        System.out.println("witness number: "+number);
        reasoner.dispose();
        return number;
    }

    public static void testLdBetweenMineAndLethe(String dictPath,String pathOnto1,String pathOnto2 )throws Exception
    {
        if(dictPath.charAt(dictPath.length()-1) != '/') dictPath += "/";
        String title = "file,tool,time,mem,uisize,afterForgettingAxiomsSize,beforeForgettingAxiomsSize,definersSize";
        //String dictPath = "/Users/liuzhao/Desktop/NCBO/CVDO/";
        //String pathOnto1 = "2016.owl";
        //String pathOnto2 = "2020.owl";
        String filelog = "log"+"_8.24aiiitest.txt";
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
        OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
        OWLOntology onto1 = null,onto2 = null;
        try {
            System.out.println("begin loaded");
            long now = System.currentTimeMillis();
            onto1 = manager1.loadOntologyFromOntologyDocument(new File(pathOnto1));
            System.out.println("onto1 load time " + (System.currentTimeMillis() - now));
            System.out.println("onto1 loaded");
            onto2 = manager2.loadOntologyFromOntologyDocument(new File(pathOnto2));
            System.out.println("onto2 loaded");
        }catch (Exception e) {
            System.err.println(dictPath+" IO error");
            writeFile.writeFile(dictPath+"errorIO2.txt"," IO error"+'\n');
            return;
        }



        final String log = pathOnto2;
        time = 0;
        mem = 0;
        afterForgettingAxiomsSize = 0;
        beforeForgettingAxiomsSize = 0;
        elkEntailment.hasChecked_OnO2.clear();
        AtomicConcept.setDefiner_index(1);
        Set<OWLClass> forgettingConcepts = new LinkedHashSet<>(Sets.difference(onto2.getClassesInSignature(), onto1.getClassesInSignature()));
        Set<OWLObjectProperty> forgettingRoles = new LinkedHashSet<>(Sets.difference(onto2.getObjectPropertiesInSignature(), onto1.getObjectPropertiesInSignature()));
        Set<OWLEntity> forgettingSignatures = Sets.union(new HashSet<>(forgettingConcepts), new HashSet<>(forgettingRoles));
        /*
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto2, ModuleType.STAR);
        Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto2.getSignature(), forgettingSignatures));
        Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
        Set<OWLAxiom> moduleOnto_2OnCommonSig2 = new HashSet<>();
        System.out.println("module finished");
        for (OWLAxiom axiom : moduleOnto_2OnForgettingSig) {
            if (axiom instanceof OWLLogicalAxiom) {
                moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                moduleOnto_2OnCommonSig2.add(axiom);
            }
        }
        OWLOntology afterDeleteNotELHAxioms = manager2.createOntology(moduleOnto_2OnCommonSig2);
        List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);

         */

        System.out.println("begin mine");
        OWLOntology myForgettingUI = MyForgetting(dictPath,filelog,log,new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto2);
        int number1 = -1;
        if(success == 1 && isExtra == 0) {
            saveOntology(manager2, myForgettingUI, dictPath + "uiPrototype.owl");
            number1 = checkWitnessAndSave(manager2, onto1, myForgettingUI, dictPath + "witnessPrototype.owl");
            if (number1 < 0) {
                writeFile.writeFile(dictPath + "hermiterror.txt",number1 + " "+'\n');
                return;
            }
        }
        writeFile.writeFile(dictPath + filelog, number1 + " " + '\n');





        System.out.println("begin lethe");
        OWLOntology letheForgettingUI = LetheForgetting(dictPath,filelog,log,forgettingSignatures,onto2);
        int number2 = -1;
        if(success == 1 && isExtra == 0) {
            saveOntology(manager2, letheForgettingUI, dictPath + "uiLethe.owl");
            number2 = checkWitnessAndSave(manager2, onto1, letheForgettingUI, dictPath + "witnessLethe.owl");


        }
        writeFile.writeFile(dictPath+filelog,number2+" "+'\n');


        // check witness in letheui and mineui
/*
        //check if lethe can entail mine
        OWLReasoner reasoner = new Reasoner(new Configuration(),letheForgettingUI);
        int number = 0 ;
        for(OWLAxiom axiom : myForgettingUI.getLogicalAxioms()){
            number++;
            System.out.println(axiom);
            if(!reasoner.isEntailed(axiom)){
                throw new Exception("not entailed");
            }else{
                System.out.println(number+" "+myForgettingUI.getLogicalAxioms().size());
            }
        }
        reasoner.dispose();
        System.out.println("good! myUI is entailed by LetheUI!");
        */

    }

    private static OWLClassExpression getRightExpression(OWLAxiom axiom)throws Exception{
        if(axiom instanceof OWLEquivalentClassesAxiom){
            for(OWLSubClassOfAxiom a : ((OWLEquivalentClassesAxiom)axiom).asOWLSubClassOfAxioms()){
                return a.getSuperClass();
            }
            throw new Exception();
        }else{
            return  ((OWLSubClassOfAxiom)axiom).getSuperClass();
        }
    }
    /**
     *
     * 检查V和O1的defined concept定义的改变，是削减还是增强，还是不变
     * @param o1
     * @param v
     */
    public static void checkDefinedConceptChange(OWLOntology o1, OWLOntology v)throws Exception{
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = manager.getOWLDataFactory();
        int type1 = 0,type2 = 0,type3 = 0, type4 = 0;
        Set<OWLClass> notChangedConcepts = new HashSet<>();//定义不变的class
        Set<OWLClass> reinforcedConcepts = new HashSet<>();//被定义加强的class
        Set<OWLClass> weakenConcepts= new HashSet<>();//被削弱的class
        Set<OWLClass> weakenOnGeneralNotChangedOnCommonConcept = new HashSet<>();//在共有符号上定义不变，在全部符号上定义削弱的class
        Set<OWLClass> otherConcepts = new HashSet<>();//其他改变的本体
        OWLReasoner  reasoner = new Reasoner.ReasonerFactory().createReasoner(o1);
        Map<OWLClass,Set<OWLLogicalAxiom>> mapO1 = new HashMap<>();
        Map<OWLClass,Set<OWLLogicalAxiom>> mapV = new HashMap<>();
        for(OWLLogicalAxiom axiom : o1.getLogicalAxioms()){
          for(OWLClass c : axiom.getClassesInSignature()){
              mapO1.putIfAbsent(c,new HashSet<>());
              mapO1.get(c).add(axiom);
          }
        }
        for(OWLLogicalAxiom axiom : v.getLogicalAxioms()){
          for(OWLClass c : axiom.getClassesInSignature()){
              mapV.putIfAbsent(c,new HashSet<>());
              mapV.get(c).add(axiom);
          }
        }
        int i = 0;
        for(OWLClass c : mapV.keySet()){
          if(mapO1.containsKey(c)){
             OWLAxiom definition1 = generateDefinition(mapO1.get(c),c);
             OWLAxiom definition2 = generateDefinition(mapV.get(c),c);
             OWLClassExpression right1 = getRightExpression(definition1);
             OWLClassExpression right2 = getRightExpression(definition2);
             OWLSubClassOfAxiom axiom1 = factory.getOWLSubClassOfAxiom(right1,right2);
             OWLSubClassOfAxiom axiom2 = factory.getOWLSubClassOfAxiom(right2,right1);
             boolean entailed1 = reasoner.isEntailed(axiom1);
             boolean entailed2 = reasoner.isEntailed(axiom2);
              //分四种情况，每种情况里还有四种情况（B = c, B in C, C in B, other,  B和C是A=B或AinB 中的B 和 AinC或A=C中的C）
             if(definition1 instanceof OWLEquivalentClassesAxiom && definition2 instanceof  OWLEquivalentClassesAxiom){

                 type1++;
                 if(entailed1 && entailed2)notChangedConcepts.add(c);
                 else if(entailed1){
                     weakenConcepts.add(c);
                 }else if(entailed2){
                     reinforcedConcepts.add(c);
                 }else{
                     otherConcepts.add(c);
                 }



             }else if(definition1 instanceof OWLSubClassOfAxiom && definition2 instanceof OWLSubClassOfAxiom){

                 type2++;
                 if(entailed1 && entailed2)notChangedConcepts.add(c);
                 else if(entailed1){
                     weakenConcepts.add(c);
                 }else if(entailed2){
                     reinforcedConcepts.add(c);
                 }else{
                     otherConcepts.add(c);
                 }


             }else if(definition1 instanceof OWLSubClassOfAxiom && definition2 instanceof  OWLEquivalentClassesAxiom){

                 type3++;
                 if(entailed1 && entailed2) reinforcedConcepts.add(c);
                 else if(entailed1){
                     weakenConcepts.add(c);
                 }else if(entailed2){
                     reinforcedConcepts.add(c);
                 }else{
                     otherConcepts.add(c);
                 }


             }else{
                 type4++;
                 if(entailed1 && entailed2){
                     weakenOnGeneralNotChangedOnCommonConcept.add(c);
                 }else if(entailed2){
                     reinforcedConcepts.add(c);
                 }else{
                     otherConcepts.add(c);
                 }
             }
          }
          System.out.println(i++ + " "+ mapV.keySet().size());
        }
        reasoner.dispose();
        System.out.println(type1+" "+type2+" "+type3+" "+type4);
        System.out.println(notChangedConcepts.size()+" "+reinforcedConcepts.size()+" "+otherConcepts.size()+" "+weakenConcepts.size()+" "+weakenOnGeneralNotChangedOnCommonConcept.size());
    }

    public static OWLAxiom generateDefinition(Set<OWLLogicalAxiom> set,OWLClass c)throws Exception{
        Set<OWLLogicalAxiom> A_left = new HashSet<>();
        Set<OWLLogicalAxiom> A_right = new HashSet<>();
        Set<OWLLogicalAxiom> A_equiv = new HashSet<>();
        for(OWLLogicalAxiom axiom : set){
            if(axiom instanceof OWLEquivalentClassesAxiom){
                OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
                Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
                for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
                    if(owlSCOA.getSubClass().equals(c)){
                        A_equiv.add(axiom);
                    }
                    break;
                }
            }else if(axiom instanceof OWLSubClassOfAxiom){
                OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
                if(owlSCOA.getSubClass().equals(c)){
                    A_left.add(axiom);
                }
                else if(owlSCOA.getSuperClass().equals(c)){
                    A_right.add(axiom);
                }
            }
        }
        if(A_equiv.size()>1) throw  new Exception();
        if(A_equiv.size() == 1) return A_equiv.iterator().next();
        else if(A_left.size() > 0){
            Set<Formula> rightOfA = new HashSet<>();
            Converter ct = new Converter();
            BackConverter bc = new BackConverter();
            List<Formula> A_leftFormulas = ct.AxiomsConverter(A_left);
            for(Formula formula : A_leftFormulas){
                rightOfA.add(formula.getSubFormulas().get(1));
            }

            Formula right1 = And.getAnd(rightOfA); //right1 为 A in B and C and D 中的 B and C and D

            for(OWLLogicalAxiom axiom : A_right){
                Set<OWLLogicalAxiom> temp_ = new HashSet<>();
                temp_.add(axiom);
                List<Formula> A_rightFormulas = ct.AxiomsConverter(temp_);//A_rightFormulas的大小一定是1
                Formula A_right_leftOfA = A_rightFormulas.get(0).getSubFormulas().get(0);//为 B and C and D in A 中的 B and C and D
                if(A_right_leftOfA instanceof And && right1 instanceof And &&
                        right1.getSubformulae().containsAll(A_right_leftOfA.getSubformulae())){// 防止出现 A in B and C and D 和 B and C in A 不能合并的现象
                    return bc.toOWLAxiom(new Equivalence(ct.getConceptfromClass(c),A_right_leftOfA));
                }
                else if(A_right_leftOfA.equals(right1))
                    return bc.toOWLAxiom(new Equivalence(ct.getConceptfromClass(c),right1));
            }
            /*
            List<Formula> A_rightFormulas = ct.AxiomsConverter(A_right);
            for(Formula formula : A_rightFormulas){
                if(formula.getSubFormulas().get(0).equals(right1)){
                    return bc.toOWLAxiom(new Equivalence(ct.getConceptfromClass(c),right1));
                }
            }

             */
            return bc.toOWLAxiom(new Inclusion(ct.getConceptfromClass(c),right1));

        }else{
            Formula f = new Inclusion(new Converter().getConceptfromClass(c),TopConcept.getInstance());
            return new BackConverter().toOWLAxiom(f);
        }
    }


    public static void testUI(String corpus, String part,double rate)throws Exception{
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/dataSet/"+corpus+"/"+part+"/";
        //String dictPath = "/Users/liuzhao/nju/NCBO/data/";
        String filelog = "log"+rate+part+"LICSDepth.txt";
        String title = "isLethe,fileName,LogicalAxiomsSize,RolesSize,ConceptsSize,GCISize,GCIRolesSize,GCIConceptSize,rate,time,memory,timeOut,MemoryOut," +
                "isSuccess,isExtra,afterForgettingAxiomsSize,beforeForgettingAxiomsSize,definer,optimizenum1,optimizenum2,optimizenum3,optimizenum4,optimizetim3,depthMean,depthMedian,depthMax\n";
       //writeFile.writeFile(dictPath+filelog,title);//写入title
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        int circle = 3;//重复10次实验
        int isLethe = 0;
        //删除上一次没做完的
        ArrayList<String> temp = readFile.readFile(dictPath+filelog);//
        while(temp.size() !=0 && temp.get(temp.size()-1).charAt(0) != '1'){
            File file = new File(dictPath+filelog);
            if(file.exists()) file.delete();
            for(int i = 0; i < temp.size()-1 ; i++)
                writeFile.writeFile(dictPath+filelog,temp.get(i)+"\n");
            temp = readFile.readFile(dictPath+filelog);
        }

        ArrayList<String> allFile = getFileName(dictPath);
        for(String path : allFile){
            if(!path.contains(".owl")) continue;
            int hasReadMine = 0;
            ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);
            for(String str : hasRecord) {
                if (str.contains(path) && (str.charAt(0)- (int)('1')) == 0) {
                    hasReadMine++;
                }

            }
            if(hasReadMine >= circle) continue;
            System.out.println("File:"+path);

            for( ; hasReadMine < circle ; hasReadMine++){
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                onto = manager1.loadOntologyFromOntologyDocument(new File(path));

                // 统计基本的信息
                int logicalsize = onto.getLogicalAxioms().size();
                int rolesize = onto.getObjectPropertiesInSignature().size();
                int conceptsize = onto.getClassesInSignature().size();
                int GCIsize = onto.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs = onto.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts = new LinkedHashSet<>();
                for(OWLClassAxiom axiom : GCIs){
                    GCIconcepts.addAll(axiom.getClassesInSignature());
                    GCIroles.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize = GCIroles.size();
                int GCIconceptsize = GCIconcepts.size();

                //data
                Set<OWLClass>concepts = onto.getClassesInSignature();
                Set<OWLObjectProperty>roles = onto.getObjectPropertiesInSignature();
                List<OWLClass> conceptList = new ArrayList<>(concepts);
                List<OWLObjectProperty>roleList = new ArrayList<>(roles);
                final String log = path+","+logicalsize+","+rolesize+","+conceptsize+","+GCIsize+","+GCIrolesize+","+GCIconceptsize+","+rate;
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                beforeForgettingAxiomsSize = 0;
                elkEntailment.hasChecked_OnO2.clear();
                AtomicConcept.setDefiner_index(1);
                System.out.println("forgetting roles :"+(int) (rate * rolesize));
                System.out.println("forgetting concepts :"+(int) (rate * conceptsize));
                System.out.println(hasReadMine);
                List<OWLClass> forgettingConcepts = getSubStringByRadom2(conceptList, (int) (rate * conceptsize));
                //List<OWLObjectProperty> forgettingRoles = getSubStringByRadom1(roleList, (int) (rate * rolesize));
                List<OWLObjectProperty> forgettingRoles = new ArrayList<>();
                Set<OWLEntity> forgettingSignatures = Sets.union(new HashSet<>(forgettingConcepts), new HashSet<>(forgettingRoles));
                System.out.println("begin mine");
                OWLOntology myForgettingUI = MyForgetting(dictPath,filelog,log,new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto);
                //System.out.println("begin last");
               // OWLOntology lastForgettingUI = LastForgetting(dictPath,filelog,log,new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto);
                System.out.println("begin lethe");
                OWLOntology letheForgettingUI = LetheForgetting(dictPath,filelog,log,forgettingSignatures,onto);
                /*
                       OWLReasoner      reasoner = new ReasonerFactory().createReasoner(letheForgettingUI);

                int number = 0 ;
                for(OWLAxiom axiom : myForgettingUI.getLogicalAxioms()){
                    number++;
                    System.out.println(axiom);
                    if(!reasoner.isEntailed(axiom)){
                        throw new Exception("not entailed");
                    }else{
                        System.out.println(number+" "+myForgettingUI.getLogicalAxioms().size());
                    }
                }
                System.out.println(letheForgettingUI.getLogicalAxiomCount()+" "+onto.getLogicalAxiomCount());
                System.out.println("good! myUI is entailed by LetheUI!");

                 */
            }


        }
    }

    public static OWLOntology checkWitness(OWLOntology onto1,OWLOntology onto2,OWLOntology ui,String pathlog,String witnesspath)throws Exception{
        System.out.println("starting reasoning");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        Set<OWLClass> c_sig_1 = onto1.getClassesInSignature();
        Set<OWLClass> c_sig_2 = onto2.getClassesInSignature();
        Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(c_sig_2, c_sig_1));
        Set<OWLObjectProperty> r_sig_1 = onto1.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig_2 = onto2.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(r_sig_2, r_sig_1));

        Set<OWLEntity> forgettingSignatures = new HashSet<>();
        forgettingSignatures.addAll(r_sig);
        forgettingSignatures.addAll(c_sig);
        int uisize = ui.getLogicalAxiomCount();
        Set<OWLLogicalAxiom> uiSet = ui.getLogicalAxioms();
        // as we compute the uniform_interpolant on module, we must add the axioms in O2 with no new signatures because they may be explicit witness.
        for(OWLLogicalAxiom axiom : onto2.getLogicalAxioms()){
            if(Sets.intersection(axiom.getSignature(),forgettingSignatures).size() == 0 ){
                uiSet.add(axiom);
            }
        }
        int num_add_all_commonSig_axioms_fromO2 = uiSet.size();
        uiSet = Sets.difference(uiSet,onto1.getLogicalAxioms());
        int numadd_all_commonSig_axioms_fromO2_subO1 = uiSet.size();
        System.out.println(uisize+" "+num_add_all_commonSig_axioms_fromO2+" "+numadd_all_commonSig_axioms_fromO2_subO1);
        OWLOntology witness_complete_onto = manager.createOntology();
        OWLOntology witness_explicit_onto = manager.createOntology();
        OWLOntology witness_implicit_onto = manager.createOntology();
        //OWLReasoner hermit =  new ElkReasonerFactory().createReasoner(onto1);
        OWLReasoner  hermit = new Reasoner.ReasonerFactory().createReasoner(onto1);
        int numexplicit = 0;
        int numimplicit = 0;
        int step = 0;
        int all = uiSet.size();
        for(OWLAxiom axiom:uiSet){
            step++;
            //if(elkEntailment.entailed(hermit,axiom)){
               // BiMap<String, Integer> biMap = HashBiMap.create();
                if(hermit.isEntailed(axiom)){

            }
            else{
                manager.applyChange(new AddAxiom(witness_complete_onto, axiom));
                if(onto2.getAxioms().contains(axiom)){
                    manager.applyChange(new AddAxiom(witness_explicit_onto, axiom));

                    numexplicit++;
                    System.out.println("explicit "+numexplicit);

                }
                else{
                    manager.applyChange(new AddAxiom(witness_implicit_onto, axiom));
                    numimplicit++;
                    System.out.println("implicit "+numimplicit);
                }

            }
            System.out.println(step+" "+all);
        }

        writeFile.writeFile(pathlog,numexplicit+","+numimplicit+"\n");
        System.out.println(numexplicit+","+numimplicit+","+num_add_all_commonSig_axioms_fromO2+","+numadd_all_commonSig_axioms_fromO2_subO1+"\n");
        OutputStream os_complete;
        OutputStream os_explicit;
        OutputStream os_implicit;
        os_complete = new FileOutputStream(new File(witnesspath + "_witness_complete.owl"));
        manager.saveOntology(witness_complete_onto, os_complete);
        os_explicit = new FileOutputStream(new File(witnesspath + "_witness_explicit.owl"));
        manager.saveOntology(witness_explicit_onto, os_explicit);
        os_implicit = new FileOutputStream(new File(witnesspath + "_witness_implicit.owl"));
        manager.saveOntology(witness_implicit_onto, os_implicit);

        return witness_complete_onto;
    }
    public static void mergeWitness(OWLOntology implicitwitness,OWLOntology explicitwitness,String log){
        HashMap<Formula,HashSet<Formula>> map = new HashMap<>();
        Converter ct = new Converter();
        List<Formula> formula_list = ct.OntologyConverter(implicitwitness);
        int step = 0;
        for(Formula formula : formula_list){
            step++;
            Formula l1 = formula.getSubFormulas().get(0);
            Formula r1 = formula.getSubFormulas().get(1);
            if(map.containsKey(l1)){
                if(r1 instanceof And){
                    map.get(l1).addAll(r1.getSubformulae());
                }
                else map.get(l1).add(r1);

            }
            else{
                if(r1 instanceof And){
                    HashSet<Formula> temp = new HashSet<>();
                    temp.addAll(r1.getSubformulae());
                    map.put(l1,temp);
                }
                else{
                    HashSet<Formula> temp = new HashSet<>();
                    temp.add(r1);
                    map.put(l1,temp);
                }
            }
        }
        System.out.println("-------");
        BackConverter bc = new BackConverter();
        List<Formula> afterMerge = new ArrayList<>();
        for(Formula key : map.keySet()){
            HashSet<Formula>and = map.get(key);
            Formula r = null;
            if(and.size() > 1)
                r =  And.getAnd(and);
            for(Formula f: and){
                r  = f;
            }
            Formula inclusion = new Inclusion(key,r);
            afterMerge.add(inclusion);

        }
        Set<OWLAxiom> ui = bc.toOWLAxioms(afterMerge);
        int implicit = Sets.difference(ui,explicitwitness.getLogicalAxioms()).size();
        System.out.println(implicit);
        System.out.println(ui.size());
    }
    public static void check3(String name)throws Exception{
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/";
        OWLOntology onto =  OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+name));
        System.out.println("loaded");

        Converter ct = new Converter();
        List<Formula> list = ct.OntologyConverter(onto);
        int num = 0;
        System.out.println("started");
        for(Formula formula : list){
            if(formula.getSubFormulas().get(1) instanceof TopConcept)
                num++;
        }
        System.out.println(num);
    }

    public static void choose(){
        String dictPath = "/Users/liuzhao/nju/NCBO/data/log0.1corpus1_n.txt";
        List<String> now = readFile.readFile(dictPath);
        String last = "owl";
        String tagPath = "/Users/liuzhao/nju/NCBO/data/log0.1corpus1_n_temp.txt";

        for(String s1: now){
            int t1 = s1.indexOf("owl");
            int t2 = last.indexOf("owl");
            if(t1 == t2){

            }
            else{
                writeFile.writeFile(tagPath,s1+"\n");

            }
            last = s1;

        }
    }
    public static void statistics()throws Exception{
        String defner = "http://snomed.info/id/128289001";
        String dictPath = "/Users/liuzhao/Desktop/";
        AtomicConcept concept= new AtomicConcept(defner);
        OWLOntology onto = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201707.owl"));
        int pos = 0, neg = 0;
        FChecker ec = new FChecker();
        EChecker ec2 = new EChecker();
        List<Formula> formulas = new Converter().OntologyConverter(onto);
        int step = 0;
        Set<Formula> positive_star_premises = new LinkedHashSet<>(); // C in A   1
        Set<Formula> positive_exists_premises = new LinkedHashSet<>(); //  C in exist r. A   2
        Set<Formula> positive_exists_and_premises = new LinkedHashSet<>(); //  C in exist r. (A and B)   3
        Set<Formula> negative_star_premises = new LinkedHashSet<>(); // A in G  4
        Set<Formula> negative_star_and_premises = new LinkedHashSet<>(); // A and F in G  5
        Set<Formula> negative_exists_premises = new LinkedHashSet<>(); //  exist r. A in G   6
        Set<Formula> negative_star_and_exists_premises = new LinkedHashSet<>(); // exists r.A and F in G   7
        Set<Formula> negative_exists_and_premises = new LinkedHashSet<>(); //  exist r. (A and D) in G   8
        Set<Formula> negative_star_and_exists_and_premises = new LinkedHashSet<>(); //  exist r. (A and D) and F in G   9
        for(Formula formula: formulas){
            pos+= ec.positive(concept,formula);
            neg+= ec.negative(concept,formula);
            System.out.println(formulas.size()+" "+step);
            step++;
            Formula subsumee = formula.getSubFormulas().get(0);
            Formula subsumer = formula.getSubFormulas().get(1);
            if (!ec2.isPresent(concept, formula)) {

            }
            if (subsumer.equals(concept)) {
                positive_star_premises.add(formula);

            }
            if (subsumer instanceof Exists &&
                    ec2.isPresent(concept, subsumer)) {

                if(subsumer.getSubFormulas().get(1).equals(concept))positive_exists_premises.add(formula);
                else positive_exists_and_premises.add(formula);

            }
            if (subsumee.equals(concept)) {
                negative_star_premises.add(formula);

            }
            if (subsumee instanceof And) {
                if (subsumee.getSubformulae().contains(concept)) { ////// changed
                    negative_star_and_premises.add(formula);
                }

                for(Formula f : subsumee.getSubformulae()){
                    if(ec2.isPresent(concept,f)){
                        System.out.println(subsumee);
                        if(f.getSubFormulas().get(1).equals(concept)){
                            negative_star_and_exists_premises.add(formula);
                        }
                        else{
                            negative_star_and_exists_and_premises.add(formula);
                        }
                    }
                }


            }
            if (subsumee instanceof Exists) {
                if(subsumee.getSubFormulas().get(1).equals(concept)) negative_exists_premises.add(formula);
                else negative_exists_and_premises.add(formula);

            }
        }
        System.out.println(pos+" "+neg);
        System.out.println("1  "+ positive_star_premises.size());
        System.out.println("1  "+ positive_exists_premises.size());

        System.out.println("1  "+ positive_exists_and_premises.size());

        System.out.println("1  "+ negative_star_premises.size());

        System.out.println("1  "+ negative_star_and_premises.size());
        System.out.println("1  "+ negative_exists_premises.size());
        System.out.println("1  "+ negative_star_and_exists_premises.size());
        System.out.println("1  "+ negative_exists_and_premises.size());
        System.out.println("1  "+ negative_star_and_exists_and_premises.size());
    }
    public static void statisticsBio() throws Exception{

        List<Integer> tbox = new ArrayList<>();
        List<Integer> Nc = new ArrayList<>();
        List<Integer> Nr = new ArrayList<>();

        String dictPath = "/Users/liuzhao/nju/NCBO/data/PART3/";
        List<String> now = getFileName(dictPath);
        int sum1 = 0,sum2 = 0,sum3 = 0;
        for(String s: now){
            OWLOntology onto = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(s));
            Nr.add(onto.getObjectPropertiesInSignature().size());
            Nc.add(onto.getClassesInSignature().size());
            tbox.add(onto.getLogicalAxiomCount());
            sum1+=onto.getClassesInSignature().size();
            sum2+=onto.getObjectPropertiesInSignature().size();
            sum3+=onto.getLogicalAxiomCount();

        }
        Collections.sort(tbox);
        Collections.sort(Nc);
        Collections.sort(Nr);
        int a = Nc.get(0), b = Nc.get(Nc.size()-1);
        System.out.println(a+" "+b);
        List<Integer> l1 = Nc.subList((int)(Nc.size()*0.1),Nc.size());
        int sum = 0;
        for(Integer i : l1 ){
            sum+=i;
        }

        sum = sum/l1.size();
        System.out.println(Nc.get(0)+" "+Nc.get(Nc.size()-1)+" "+Nc.get(Nc.size()/2)+" "+sum1/Nc.size()+" "+sum);
        List<Integer> l2 = Nr.subList((int)(Nr.size()*0.1),Nr.size());
        sum = 0;
        for(Integer i : l2 ){
            sum+=i;
        }
        sum = sum/l2.size();
        System.out.println(Nr.get(0)+" "+Nr.get(Nr.size()-1)+" "+Nr.get(Nr.size()/2)+" "+sum2/Nr.size()+" "+sum);
        List<Integer> l3 = tbox.subList((int)(tbox.size()*0.1),tbox.size());
        sum = 0;
        for(Integer i : l3 ){
            sum+=i;
        }
        sum = sum/l3.size();
        System.out.println(tbox.get(0)+" "+tbox.get(tbox.size()-1)+" "+tbox.get(tbox.size()/2)+" "+sum3/tbox.size()+" "+sum);

    }
    public static List<OWLOntology> testLDiff(String dictPath,String nameonto1,String nameonto2)throws Exception{
        String filelog = "logtemp"+".txt";
        ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);

        String title = "fileName_O1,fileName_O2,LogicalAxiomsSize_O1,LogicalAxiomsSize_O2,RolesSize_O1,RolesSize_O2,ConceptsSize_O1,ConceptsSize_O2," +
                "GCISize_O1,GCISize_O2,GCIRolesSize_O1,GCIRolesSize_O2,GCIConceptSize_O1,GCIConceptSize_O2,newLogicalRoleSize,newLogicalConceptSize,newLogicalRoleSizeOccuredInGCI,newLogicalConceptSizeOccuredInGCI,time," +
                "memory,timeOut,MemoryOut," +"isSuccess,isExtra,UI_size,explicit_witness,implicit_witness\n";
        // writeFile.writeFile(dictPath+filelog,title);
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        ArrayList<String> now = getFileName(dictPath);
        List<OWLOntology> ans = new ArrayList<>();
        saveMetrics metrics = new saveMetrics();

        for(String path : now) {
            for (String path2 : now) {
                if(path.equals(path2)) continue;
                int hasRead = 0;
                for (String temp : hasRecord) {
                    if (temp.contains(path+","+path2)) {
                        hasRead = 1;
                        break;
                    }
                }

                //if(path.contains("202001")) continue;
                if(!(path.contains(nameonto1) && path2.contains(nameonto2))) continue;

                if (hasRead == 1) continue;
                if (!path.contains(".owl") || !path2.contains(".owl")) continue;
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                String pathuiNCIT = dictPath+path.substring(path.length()-9,path.length()-4)+path2.substring(path2.length()-9,path2.length()-4)+"temp2.owl";
                System.out.println(pathuiNCIT);
                System.out.println(path);
                System.out.println(path2);

                OWLOntology onto1 = manager1.loadOntologyFromOntologyDocument(new File(path));
                System.out.println("onto1 load1");
                // 统计基本的信息
                int logicalsize1 = onto1.getLogicalAxioms().size();
                int rolesize1 = onto1.getObjectPropertiesInSignature().size();
                int conceptsize1 = onto1.getClassesInSignature().size();
                int GCIsize1 = onto1.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs1 = onto1.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles1 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts1 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs1) {
                    GCIconcepts1.addAll(axiom.getClassesInSignature());
                    GCIroles1.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize1 = GCIroles1.size();
                int GCIconceptsize1 = GCIconcepts1.size();


                OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
                OWLOntology onto2 = manager2.loadOntologyFromOntologyDocument(new File(path2));
                System.out.println("onto2 load1");
                // 统计基本的信息
                int logicalsize2 = onto2.getLogicalAxioms().size();
                int rolesize2 = onto2.getObjectPropertiesInSignature().size();
                int conceptsize2 = onto2.getClassesInSignature().size();
                int GCIsize2 = onto2.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs2 = onto2.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles2 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts2 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs2) {
                    GCIconcepts2.addAll(axiom.getClassesInSignature());
                    GCIroles2.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize2 = GCIroles2.size();
                int GCIconceptsize2 = GCIconcepts2.size();


                //data

                Set<OWLClass> concepts1 = onto1.getClassesInSignature();
                Set<OWLObjectProperty> roles1 = onto1.getObjectPropertiesInSignature();

                Set<OWLClass> concepts2 = onto2.getClassesInSignature();
                Set<OWLObjectProperty> roles2 = onto2.getObjectPropertiesInSignature();

                //diff data

                Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(concepts2, concepts1));
                Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(roles2, roles1));
                Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
                Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);
                Set<OWLEntity> forgettingSignatures = new HashSet<>();
                forgettingSignatures.addAll(r_sig);
                forgettingSignatures.addAll(c_sig);

                String log = path + "," + path2+","+logicalsize1 + "," +logicalsize2+","+ rolesize1 + "," +rolesize2+","+
                        conceptsize1 + "," +conceptsize2+","+ GCIsize1 + "," + GCIsize2 + "," +GCIrolesize1 + "," +GCIrolesize2 + "," +
                        GCIconceptsize1 + ","+ GCIconceptsize2 + ","+ Sets.difference(roles2,roles1).size()+","+Sets.difference(concepts2,concepts1).size()+","+
                        Sets.intersection(GCIroles2, Sets.difference(roles2,roles1)).size()+","+Sets.intersection(GCIconcepts2, Sets.difference(concepts2,concepts1)).size();

                System.out.println("gci " +GCIsize2);
                nowLog = log ;
                System.out.println(nowLog);
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                Forgetter fg = new Forgetter();
                isExtra = 0;
                success = 1;
                witness_explicit_onto = 0;
                witness_implicit_onto = 0;
                elkEntailment.hasChecked_OnO2 = new HashMap<>();
                AtomicConcept.setDefiner_index(1);
                SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto2, ModuleType.STAR);
                Set<OWLAxiom> moduleOnto_2OnCommonSig = extractor.extract(Sets.difference(onto2.getSignature(),forgettingSignatures));
                Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
                for (OWLAxiom axiom : moduleOnto_2OnCommonSig) {
                    if (axiom instanceof OWLLogicalAxiom) {
                        moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                    }
                }
                System.out.println(moduleOnto_2OnCommonSig_logical.size()+" "+moduleOnto_2OnCommonSig.size());
                System.out.println("module finished");
                List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);
                try {
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    long time1 = System.currentTimeMillis();
                    System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                            + role_set.size() + "] role names from [" + moduleOnto_2OnCommonSig_logical.size() + "] normalized axioms");
                    List<Formula> ui = fg.Forgetting(r_sig, c_sig, onto2,metrics);

                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    //elkEntailment.check(onto2,ui);
                    time += (time2 - time1);
                    mem += (mem1 - mem2);
                    Set<OWLAxiom> uniform_interpolant = bc.toOWLAxioms(ui);
                    saveUI(uniform_interpolant,pathuiNCIT);
                    ans.add(onto1);
                    ans.add(onto2);
                    ans.add(bc.toOWLOntology(ui));
                    afterForgettingAxiomsSize = uniform_interpolant.size();


                } catch (OutOfMemoryError e) {
                    nowLog = nowLog + ",0,0,0,1,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("outofmemory");
                    e.printStackTrace();
                    success = 0;
                } catch (StackOverflowError e) {
                    nowLog = nowLog + ",0,0,0,2,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("stackoverflow");
                    success = 0;
                }



                if (success == 1 && isExtra == 0) {
                    nowLog = nowLog + "," + time  + "," + mem / 1024 / 1024  + ",0,0,1,0," + afterForgettingAxiomsSize  + ",";
                    writeFile.writeFile(dictPath + filelog, nowLog);


                }


                if (success == 1 && isExtra != 0) {
                    nowLog = nowLog + ",0,0,0,0,0," + isExtra + ",0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                }

            }

        }
        return ans;
    }
    public static void testLethe() throws Exception{
        AlchTBoxForgetter letheForgetter = new AlchTBoxForgetter();
        OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/dataSet/Oxford-ISG/PARTIII/00117.owl"));
        Set<OWLEntity> symbols = new HashSet<>();
        for(OWLClass o : onto1.getClassesInSignature()){
            symbols.add(o);
            break;
        }
        letheForgetter.forget(onto1,symbols);
    }
    public static void testGhadah()throws Exception{
        OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/go-2021-02-01.owl"));
        OWLOntology itui = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/goslim_agr.owl"));
        Set<OWLEntity> symbols = Sets.difference(onto1.getSignature(),itui.getSignature());
       // List<Formula> beginFormulalist = new Converter().OntologyConverter(onto1);
        Set<OWLClass> conceptSet = new HashSet<>();
        Set<OWLObjectProperty> roleSet = new HashSet<>();
        System.out.println(symbols.size());
        for(OWLEntity entity : symbols){
            if(entity instanceof OWLClass) conceptSet.add((OWLClass)entity);
            else if(entity instanceof  OWLObjectProperty) roleSet.add((OWLObjectProperty) entity);
        }
        System.out.println(conceptSet.size()+" "+roleSet.size());
        List<Formula> ui = new Forgetter().Forgetting(roleSet, conceptSet, onto1,new saveMetrics());


    }
    public static void testAAAI22()throws Exception{
        ArrayList<String> allFile = getFileName("/Users/liuzhao/Desktop/NCBOcrawler/ECSO/");
        int twoToolsFinished = 0;
        int empty = 0;
        for(String dictPath : allFile){
            int temp = 0;
            System.out.println(dictPath);
            try {
                ArrayList<String> owlName = getFileName(dictPath+"/");
                if(owlName.size() == 0) empty++;
                String onto1="",onto2 = "";
                int finished = 0;
                for(String file : owlName){
                    if(file.contains("newliuzhao.owl")){
                        onto2 = file;
                    }else if(file.contains("oldliuzhao.owl")){
                        onto1 = file;
                    }else if(file.contains("uiPrototype.owl") || (file.contains(".txt") && !file.contains("errorIO.txt")) || file.contains("errorIO2.txt")){
                        finished = 1;
                    }
                    if(file.contains("witnessPrototype.owl") || file.contains("witnessLethe.owl")){
                        temp++;
                    }
                    if(file.contains("hermiterror.txt")) finished  = 0;

                }
                if(temp == 2) twoToolsFinished++;
                if(finished == 1)continue;
                if(onto1.contains("oldliuzhao.owl") && onto2.contains("newliuzhao.owl")){
                    System.out.println(onto1+" "+onto2);
                    testLdBetweenMineAndLethe(dictPath,onto1,onto2);
                }
            }catch (NullPointerException n){
                System.out.println();
            }

        }
        System.out.println(empty);
        System.out.println(twoToolsFinished);
    }
    public static void testDefinedConceptsNums() throws Exception{
        OWLOntology on = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_202007.owl"));
        Set<OWLClass> classes = on.getClassesInSignature();
        Set<OWLLogicalAxiom> axioms = on.getLogicalAxioms();
        Set<OWLClass> left = new HashSet<>();
        Set<OWLClass> right = new HashSet<>();
        for(OWLLogicalAxiom axiom : axioms){
            if(axiom instanceof OWLEquivalentClassesAxiom){
                OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
                Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
                for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
                    left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                    right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
                    break;
                }
            }else if(axiom instanceof  OWLSubClassOfAxiom){
                OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
                left.addAll(owlSCOA.getSubClass().getClassesInSignature());
                right.addAll(owlSCOA.getSuperClass().getClassesInSignature());
            }
        }
        int leftsize = left.size();
        left.removeAll(right);
        System.out.println(classes.size()+" "+leftsize+" "+right.size() + " "+left.size() +" "+(left.size()*1.0/classes.size()));

    }
    public static void staticalAAAI22()throws Exception{
        ArrayList<String> allFile = getFileName("/Users/liuzhao/Desktop/NCBOcrawler/");
        int success = 0;
        int empty = 0;
        int errorIO = 0;
        int hermitError = 0;
        int extra = 0;
        int timeout = 0;
        int files = 0;
        int runtimeerror = 0;
        int equal = 0;
        for(String dictPath : allFile){
            System.out.println(dictPath);
            if(dictPath.contains(".DS_Store")) continue;
            files++;
            ArrayList<String> owlName = getFileName(dictPath+"/");
            if(owlName.size() == 0) {
                empty++;
                continue;
            }
            int tempfinished = 0;
            int temphermitError  =0;
            int temperrorIO = 0;
            int tempextra = 0;
            int temptimeout = 0;
            for(String file : owlName){
                if(file.contains("errorIO.txt") || file.contains("errorIO2.txt")){
                    temperrorIO++;
                }else if(file.contains("hermiterror.txt")){
                    temphermitError++;
                }else if(file.contains("timeout.txt")){
                    temptimeout++;
                }else if(file.contains("extra.txt")){
                    tempextra++;
                }else if(file.contains("log_8.24aiiitest.txt"))
                    tempfinished++;


            }
            if(temphermitError == 0 && temperrorIO == 0 && tempextra == 0 && temptimeout == 0 && tempfinished != 0 ) {
                success++;
                BufferedReader br = new BufferedReader(new FileReader(dictPath+"/log_8.24aiiitest.txt"));

                String line = null;
                int t1  =-10,t2 = -10, linePos = 0;
                int tag = 0;
                while ((line = br.readLine()) != null) {
                    if(linePos == 1) t1 =Integer.parseInt(line.replace(" ",""));
                    if(linePos == 3) t2 = Integer.parseInt(line.replace(" ",""));
                    if(line.contains("error")){
                        tag = 1;
                        break;

                    }
                    linePos++;
                }
                if(tag == 1){
                    success--;
                    runtimeerror++;
                }
                if(t1 >= 0 && t2 >= 0 && t1 != t2){
                    System.err.println("different " + dictPath);

                }else if(t1 >= 0 && t2 >= 0 && t1 == t2)equal++;

                br.close();
            }
            else if(temphermitError != 0) hermitError++;
            else if(temperrorIO != 0) errorIO++;
            else if(tempextra != 0) extra++;
            else if(temptimeout != 0) timeout++;
            else {
                System.out.println("****  "+dictPath);
                empty++;
            };



        }
        System.out.println("folder num :" + files+" empty size "+ empty +" success " +success+" equal "+equal + " timeout "+timeout + " extra " + extra +
                " erroIO "+ errorIO + " hermitError " + hermitError +" runtimeerror "+ runtimeerror);
    }
    /*
    public static void AAAIJustify()throws Exception{
        OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_201707.owl"));
        OWLOntology onto2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_201801.owl"));
        simplifier sp = new simplifier();
        Map<OWLClass,Set<OWLClass>> table2 = sp.definedConceptsRightclosure(onto2.getLogicalAxioms());
        Map<OWLClass,Set<OWLClass>> table1 = sp.definedConceptsRightclosure(onto1.getLogicalAxioms());
        Set<OWLClass> newSymbols = onto2.getClassesInSignature();
        newSymbols.removeAll(onto1.getClassesInSignature());
        for(OWLClass c : table2.keySet()){
            if(table1.containsKey(c)){
                Set<OWLClass> c_onto1 = new HashSet<>(table1.get(c));
                Set<OWLClass> c_onto2 = new HashSet<>(table2.get(c));
                c_onto1.removeAll(newSymbols);
                c_onto2.removeAll(newSymbols);
                if(!c_onto1.containsAll(c_onto2) || !c_onto2.containsAll(c_onto1)) {
                    System.out.println("different owlclass" + c);
                    System.out.println("base concept of it in onto1 :" + c_onto1);
                    System.out.println("base concept of it in onto2 :" + c_onto2);

                }

            }
        }
    }

     */
    @Test
    public void DepthEachFile()throws Exception{
        double rate = 0.3;
        String corpus = "PARTI";
        String filelog = "LICSEverydepthis.txt";
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/dataSet/Oxford-ISG/"+corpus+"/";
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        Inferencer inf = new Inferencer();
        ArrayList<String> allFile = getFileName(dictPath);

        for(String path : allFile) {
            Map<OWLClass, Set<OWLLogicalAxiom>> map = new HashMap<>();
            if (!(path.contains(".owl") || path.contains(".xml"))) continue;
            System.out.println(path);
            OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
            OWLOntology onto = manager1.loadOntologyFromOntologyDocument(new File(path));
            List<Formula> beginFormulalist = new Converter().OntologyConverter(onto);
            List<OWLClass> forgettingConcepts = getSubStringByRadom2(new ArrayList<>(onto.getClassesInSignature()), (int) (rate * onto.getClassesInSignature().size()));
            //List<OWLObjectProperty> forgettingRoles = getSubStringByRadom1(roleList, (int) (rate * rolesize));
            List<OWLObjectProperty> forgettingRoles = new ArrayList<>();
            List<Double> depthMeanMedian = getDepthMeanMedian(beginFormulalist, new HashSet<>(forgettingConcepts));
            System.out.println(depthMeanMedian);
            String log = path +","+depthMeanMedian.get(0)+","+depthMeanMedian.get(1)+","+depthMeanMedian.get(2)+"\n";
            writeFile.writeFile(dictPath+filelog,log);
        }
    }
    @Test
    public void testLICS1()throws Exception{ //type1 存在equiv左边的 type2 对于出现在左边的 只出现在A in D 这样的  type3 base concept
        // type 4 others
            String corpus = "PARTI";
            double rate = 0.5;
            String filelog = "LICSBeforeForgetting.txt";
            String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/dataSet/BioPortal/"+corpus+"/";
            Converter ct = new Converter();
            BackConverter bc = new BackConverter();
            Inferencer inf = new Inferencer();
            ArrayList<String> allFile = getFileName(dictPath);

            for(String path : allFile){
                Map<OWLClass,Set<OWLLogicalAxiom>> map = new HashMap<>();
                if(!(path.contains(".owl") || path.contains(".xml"))) continue;
                System.out.println(path);
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                OWLOntology onto = manager1.loadOntologyFromOntologyDocument(new File(path));
                int alltype = onto.getClassesInSignature().size();
                int type1 = 0, type2 = 0, type3 = 0, type4 = 0;
                Set<OWLClass> type1Type = new HashSet<>();// defined concept equiv
                Set<OWLClass> type2Type = new HashSet<>();//defined concept inclusion
                Set<OWLClass> right = new HashSet<>();
                Set<OWLClass> left = new HashSet<>();
                Set<OWLClass> type4Type = new HashSet<>();
                Set<OWLClass> leftnowSingle = new HashSet<>();
                for(OWLLogicalAxiom axiom : onto.getLogicalAxioms()){
                  //  if(axiom.toString().contains("http://purl.org/obo/owl/GO#GO_0022626")) System.out.println(axiom+"^^^");
                    if(axiom instanceof OWLEquivalentClassesAxiom){
                        Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms =
                                ((OWLEquivalentClassesAxiom)axiom).asOWLSubClassOfAxioms();
                        for(OWLSubClassOfAxiom axiom1 : owlSubClassOfAxioms){
                            if(axiom1.getSubClass() instanceof OWLClass)type1Type.add((OWLClass)axiom1.getSubClass());
                            else if(axiom1.getSuperClass() instanceof OWLClass) type1Type.add((OWLClass) axiom1.getSuperClass());
                            left.addAll(axiom1.getClassesInSignature());//todo
                           // right.addAll(axiom1.getSuperClass().getClassesInSignature());
                            break;
                        }
                        leftnowSingle.addAll(axiom.getClassesInSignature());
                    }else if(axiom instanceof OWLSubClassOfAxiom){
                        OWLSubClassOfAxiom now  = (OWLSubClassOfAxiom) axiom;
                        if(now.getSubClass() instanceof  OWLClass) type2Type.add((OWLClass) now.getSubClass());
                        else{
                            leftnowSingle.addAll(now.getSubClass().getClassesInSignature());
                        }
                        left.addAll(now.getSubClass().getClassesInSignature());
                        right.addAll(now.getSuperClass().getClassesInSignature());
                    }

                    //记录forgetting concept对应的axioms
                    Set<OWLClass> temp = axiom.getClassesInSignature();
                    for(OWLClass c : temp){
                        if(map.getOrDefault(c,null) == null){
                            map.put(c,new HashSet<>());
                        }
                        map.get(c).add(axiom);
                    }
                }
                type1 = type1Type.size();
                type2Type.removeAll(type1Type);
                type2Type.removeAll(leftnowSingle);
                type2 = type2Type.size();
                right.removeAll(left);
                right.removeAll(type1Type);
                right.removeAll(type2Type);
                type3 = right.size();
                type4 = alltype - type1 - type2 - type3;
                String nowLog = "1 "+path +" " +alltype+" "+" "+type1 +" "+ type2 +" "+ type3 +" "+ type4;
                if(type4 < 0 ) throw new Exception();
////////////////////////////////////////////
                List<OWLClass> forgettingConcepts = getSubStringByRadom2(new ArrayList<>(onto.getClassesInSignature()), (int) (rate * alltype));
                Set<OWLClass> random_forgettingConcepts = new HashSet<>(forgettingConcepts);
                Set<OWLClass> random_type1Set = Sets.intersection(random_forgettingConcepts,type1Type);
                Set<OWLClass> random_type2Set = Sets.intersection(random_forgettingConcepts,type2Type);
                Set<OWLClass> random_type3Set = Sets.intersection(random_forgettingConcepts,right);
                Set<OWLClass> random_type4Set = new HashSet<>(random_forgettingConcepts);
                random_type4Set.removeAll(random_type1Set);random_type4Set.removeAll(random_type2Set);
                random_type4Set.removeAll(random_type3Set);

                int random_type1 = random_type1Set.size();
                int random_type2 = random_type2Set.size();
                int random_type3 = random_type3Set.size();
                int random_type4 = random_forgettingConcepts.size() - random_type1-random_type2-random_type3;
                if(random_type4 != random_type4Set.size())  throw new Exception();
                if(random_type4 < 0) throw  new Exception();
                String nowLog2 ="2 "+ path +" " + random_forgettingConcepts.size()+" " + random_type1 +" "+ random_type2 +
                        " "+random_type3+" "+random_type4;

                Set<OWLLogicalAxiom> deletedAxioms = new HashSet<>();
                int random_after_type1 = random_type1,random_after_type2 =random_type2,random_after_type3 = random_type3,random_after_type4 = 0;
                Set<OWLLogicalAxiom> axioms = onto.getLogicalAxioms();
///////////////////////////////


                //先遗忘base concept
                for(OWLClass owlclass : random_type3Set){
                    Set<OWLLogicalAxiom> axiomSet = map.get(owlclass);
                    axiomSet.removeAll(deletedAxioms);
                    deletedAxioms.addAll(axiomSet);
                    List<Formula> formulas = ct.AxiomConverter_rightAnd(axiomSet);
                    List<Formula> ans = new ArrayList<>();
                    for(Formula formula : formulas){

                        if(!formula.getSubFormulas().get(1).equals(ct.getConceptfromClass(owlclass))){
                            Formula temp = inf.AckermannReplace(ct.getConceptfromClass(owlclass), formula, TopConcept.getInstance());
                            if(!TautologyChecker.isTautology(temp)) ans.add(temp); //todo 可能出现 a = b and exist r. C   把C换成了T,但应该是a in B and exist r.T


                        }
                    }
                    Set<OWLAxiom> replaced_axioms = bc.toOWLAxioms(ans);
                    for (OWLAxiom axiom : replaced_axioms) {
                        Set<OWLClass> classes = axiom.getClassesInSignature();
                        for (OWLClass c1 : classes) {
                            if (map.getOrDefault(c1, null) == null) {
                                map.put(c1, new HashSet<>());
                            }
                            map.get(c1).add((OWLLogicalAxiom) axiom);
                        }
                        axioms.add((OWLLogicalAxiom)axiom);

                    }

                }
                // 再遗忘type1
                for(OWLClass owlClass : random_type1Set) {
                    Set<OWLLogicalAxiom> axiomSet = map.get(owlClass);
                    axiomSet.removeAll(deletedAxioms);
                    deletedAxioms.addAll(axiomSet);
                    OWLLogicalAxiom axiomDefinition = null;
                    OWLClassExpression definition_of_defined_concept = null;

                    for (OWLLogicalAxiom tempaxiom : axiomSet) {
                        if (tempaxiom instanceof OWLEquivalentClassesAxiom) {
                            Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms =
                                    ((OWLEquivalentClassesAxiom) tempaxiom).asOWLSubClassOfAxioms();
                            for (OWLSubClassOfAxiom axiom1 : owlSubClassOfAxioms) {
                                if (axiom1.getSubClass() instanceof OWLClass) {
                                    if (owlClass.equals( axiom1.getSubClass())) {
                                        definition_of_defined_concept = axiom1.getSuperClass();
                                        axiomDefinition = axiom1;
                                        break;
                                    }else if (owlClass.equals(axiom1.getSuperClass())) {
                                        definition_of_defined_concept = axiom1.getSubClass();
                                        axiomDefinition = axiom1;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    if (axiomDefinition == null){ // todo
                        random_after_type1--;
                        continue;
                    }
                    axiomSet.remove(axiomDefinition);
                    List<Formula> formulas = ct.AxiomConverter_rightAnd(axiomSet);


                    Formula definition = ct.ClassExpressionConverter(definition_of_defined_concept);
                    List<Formula> ans = new ArrayList<>();
                    if (definition != null) {
                        for (Formula f : formulas) {
                            Formula temp = inf.AckermannReplace(ct.getConceptfromClass(owlClass), f, definition);
                            if(!TautologyChecker.isTautology(temp)) ans.add(temp);
                        }
                    }
                    Set<OWLAxiom> replaced_axioms = bc.toOWLAxioms(ans);
                    for (OWLAxiom axiom : replaced_axioms) {
                        Set<OWLClass> classes = axiom.getClassesInSignature();
                        for (OWLClass c1 : classes) {
                            if (map.getOrDefault(c1, null) == null) {
                                map.put(c1, new HashSet<>());
                            }
                            map.get(c1).add((OWLLogicalAxiom) axiom);
                        }
                        axioms.add((OWLLogicalAxiom) axiom);

                    }
                }
                //再计算type2，这里偷懒了没有让他去删除
                int addTotype4 = 0;
                for(OWLClass owlClass : random_type2Set){
                    Set<OWLLogicalAxiom> axiomSet = map.get(owlClass);
                    axiomSet.removeAll(deletedAxioms);
                    if(axiomSet.size() == 0){
                        random_after_type2--;
                    }else {
                        for (OWLLogicalAxiom axiom : axiomSet) {
                            if (axiom instanceof OWLSubClassOfAxiom) {
                                if (((OWLSubClassOfAxiom) axiom).getSubClass().toString().contains(owlClass.toString())) {
                                    if (!(((OWLSubClassOfAxiom) axiom).getSubClass() instanceof OWLClass)) {
                                        random_after_type2--;
                                        addTotype4++;
                                       // System.out.println(owlClass);
                                       // System.out.println(axiom);
                                        break;
                                    }

                                }
                            }
                        }
                    }
                }
                //再计算random_after_type4
                OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
                OWLOntology ontoAfter = manager2.createOntology();
                for(OWLAxiom axiom : axioms)
                    manager2.applyChange(new AddAxiom(ontoAfter, axiom));
                Set<OWLClass> classesAfter = ontoAfter.getClassesInSignature();
                classesAfter.removeAll(random_type1Set);
                classesAfter.removeAll(random_type2Set);
                classesAfter.removeAll(random_type3Set);
                random_after_type4 = Sets.intersection(random_type4Set,classesAfter).size()+addTotype4;
                int all_random_after_type = random_after_type1+random_after_type2+random_after_type3+random_after_type4;
                String nowLog3 ="3 "+ path +" " + all_random_after_type+" "+
                        random_after_type1+" " + random_after_type2 +" "+ random_after_type3 + " "+random_after_type4;
                System.out.println(nowLog);
                System.out.println(nowLog2);
                System.out.println(nowLog3);

                writeFile.writeFile(dictPath + filelog, nowLog + "\n");
                writeFile.writeFile(dictPath + filelog, nowLog2 + "\n");
                writeFile.writeFile(dictPath + filelog, nowLog3 + "\n");

                System.out.println();





            }


    }



    @Test
    public void testLICS2()throws Exception{ //type1 存在equiv左边的 type2 对于出现在左边的 只出现在A in D 这样的  type3 base concept
        // type 4 others
        String[][] dirs = new String[][]{{"1601","1607"},{"1601","1701"},{"1601","1801"},{"1607","1701"},{"1701","1707"},
                {"1701","1801"},{"1707","1801"},{"1901","1907"},{"1607","1601"},{"1701","1601"},{"1701","1607"},{"1707","1701"},
                {"1801","1701"},{"1801","1707"},{"1807","1801"},{"1901","1801"},{"1901","1807"},{"1907","1901"},{"2007","2003"}
        };
        String filelog = "LICSBeforeForgettingSNOMEDCT.txt";
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/";
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        Inferencer inf = new Inferencer();

        for(String[]dir : dirs){
            String pathO1 = dictPath +"ontology_20"+dir[0]+".owl";
            String pathO2 = dictPath + "ontology_20"+dir[1] +".owl";
            System.out.println(pathO1);
            System.out.println(pathO2);
            OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
            OWLOntology onto1 = manager1.loadOntologyFromOntologyDocument(new File(pathO1));
            System.out.println("o1 loaded");
            OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
            OWLOntology onto2 = manager2.loadOntologyFromOntologyDocument(new File(pathO2));
            System.out.println("o2 loaded");
            int alltype = onto2.getClassesInSignature().size();
            int type1 = 0, type2 = 0, type3 = 0, type4 = 0;
            Map<OWLClass,Set<OWLLogicalAxiom>> map = new HashMap<>();

            Set<OWLClass> type1Type = new HashSet<>();// defined concept equiv
            Set<OWLClass> type2Type = new HashSet<>();//defined concept inclusion
            Set<OWLClass> right = new HashSet<>();
            Set<OWLClass> left = new HashSet<>();
            Set<OWLClass> type4Type = new HashSet<>();
            Set<OWLClass> leftnowSingle = new HashSet<>();
            for(OWLLogicalAxiom axiom : onto2.getLogicalAxioms()){
                if(axiom instanceof OWLEquivalentClassesAxiom){
                    Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms =
                            ((OWLEquivalentClassesAxiom)axiom).asOWLSubClassOfAxioms();
                    for(OWLSubClassOfAxiom axiom1 : owlSubClassOfAxioms){
                        if(axiom1.getSubClass() instanceof OWLClass)type1Type.add((OWLClass)axiom1.getSubClass());
                        else if(axiom1.getSuperClass() instanceof OWLClass) type1Type.add((OWLClass) axiom1.getSuperClass());
                        left.addAll(axiom1.getClassesInSignature());//todo
                        //right.addAll(axiom1.getSuperClass().getClassesInSignature());
                        break;
                    }
                    leftnowSingle.addAll(axiom.getClassesInSignature());
                }else if(axiom instanceof OWLSubClassOfAxiom){
                    OWLSubClassOfAxiom axiom1 = (OWLSubClassOfAxiom) axiom;
                    left.addAll(axiom1.getSubClass().getClassesInSignature());
                    right.addAll(axiom1.getSuperClass().getClassesInSignature());
                    OWLSubClassOfAxiom now  = (OWLSubClassOfAxiom) axiom;
                    if(now.getSubClass() instanceof  OWLClass) type2Type.add((OWLClass) now.getSubClass());
                    else{
                        leftnowSingle.addAll(now.getSubClass().getClassesInSignature());
                    }
                }

                //记录forgetting concept对应的axioms
                Set<OWLClass> temp = axiom.getClassesInSignature();
                for(OWLClass c : temp){
                    if(map.getOrDefault(c,null) == null){
                        map.put(c,new HashSet<>());
                    }
                    map.get(c).add(axiom);
                }
            }
            type1 = type1Type.size();
            type2Type.removeAll(type1Type);
            type2Type.removeAll(leftnowSingle);
            type2 = type2Type.size();
            right.removeAll(left);
            right.removeAll(type1Type);
            right.removeAll(type2Type);
            type3 = right.size();
            type4 = alltype - type1 - type2 - type3;
            String nowLog = "1 "+pathO1+","+pathO2 +" " +alltype+" "+" "+type1 +" "+ type2 +" "+ type3 +" "+ type4;
            if(type4 < 0 ) throw new Exception();
////////////////////////////////////////////
          //  List<OWLClass> forgettingConcepts = getSubStringByRadom2(new ArrayList<>(onto.getClassesInSignature()), (int) (rate * alltype));
          //  List<OWLClass> forgettingConcepts = new ArrayList<>(Sets.difference(onto2.getClassesInSignature(),onto1.getClassesInSignature()));
            Set<OWLClass> random_forgettingConcepts = new HashSet<>(onto2.getClassesInSignature());
            random_forgettingConcepts.removeAll(onto1.getClassesInSignature());
            Set<OWLClass> random_type1Set = Sets.intersection(random_forgettingConcepts,type1Type);
            Set<OWLClass> random_type2Set = Sets.intersection(random_forgettingConcepts,type2Type);
            Set<OWLClass> random_type3Set = Sets.intersection(random_forgettingConcepts,right);
            Set<OWLClass> random_type4Set = new HashSet<>(random_forgettingConcepts);
            random_type4Set.removeAll(random_type1Set);random_type4Set.removeAll(random_type2Set);
            random_type4Set.removeAll(random_type3Set);

            int random_type1 = random_type1Set.size();
            int random_type2 = random_type2Set.size();
            int random_type3 = random_type3Set.size();
            int random_type4 = random_forgettingConcepts.size() - random_type1-random_type2-random_type3;
            if(random_type4 != random_type4Set.size())  throw new Exception();
            if(random_type4 < 0) throw  new Exception();
            String nowLog2 ="2 "+ pathO1+","+pathO2 +" " + random_forgettingConcepts.size()+" " + random_type1 +" "+ random_type2 +
                    " "+random_type3+" "+random_type4;

            Set<OWLLogicalAxiom> deletedAxioms = new HashSet<>();
            int random_after_type1 = random_type1,random_after_type2 =random_type2,random_after_type3 = random_type3,random_after_type4 = 0;
            Set<OWLLogicalAxiom> axioms = onto2.getLogicalAxioms();
///////////////////////////////


            //先遗忘base concept
            for(OWLClass owlclass : random_type3Set){
                Set<OWLLogicalAxiom> axiomSet = map.get(owlclass);
                axiomSet.removeAll(deletedAxioms);
                deletedAxioms.addAll(axiomSet);
                List<Formula> formulas = ct.AxiomConverter_rightAnd(axiomSet);
                List<Formula> ans = new ArrayList<>();
                for(Formula formula : formulas){

                    if(!formula.getSubFormulas().get(1).equals(ct.getConceptfromClass(owlclass))){
                        Formula temp = inf.AckermannReplace(ct.getConceptfromClass(owlclass), formula, TopConcept.getInstance());
                        if(!TautologyChecker.isTautology(temp)) ans.add(temp); //todo 可能出现 a = b and exist r. C   把C换成了T,但应该是a in B and exist r.T


                    }
                }
                Set<OWLAxiom> replaced_axioms = bc.toOWLAxioms(ans);
                for (OWLAxiom axiom : replaced_axioms) {
                    Set<OWLClass> classes = axiom.getClassesInSignature();
                    for (OWLClass c1 : classes) {
                        if (map.getOrDefault(c1, null) == null) {
                            map.put(c1, new HashSet<>());
                        }
                        map.get(c1).add((OWLLogicalAxiom) axiom);
                    }
                    axioms.add((OWLLogicalAxiom)axiom);

                }

            }
            // 再遗忘type1
            for(OWLClass owlClass : random_type1Set) {
                Set<OWLLogicalAxiom> axiomSet = map.get(owlClass);
                axiomSet.removeAll(deletedAxioms);
                deletedAxioms.addAll(axiomSet);
                OWLLogicalAxiom axiomDefinition = null;
                OWLClassExpression definition_of_defined_concept = null;

                for (OWLLogicalAxiom tempaxiom : axiomSet) {
                    if (tempaxiom instanceof OWLEquivalentClassesAxiom) {
                        Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms =
                                ((OWLEquivalentClassesAxiom) tempaxiom).asOWLSubClassOfAxioms();
                        for (OWLSubClassOfAxiom axiom1 : owlSubClassOfAxioms) {
                            if (axiom1.getSubClass() instanceof OWLClass) {
                                if (owlClass.equals( axiom1.getSubClass())) {
                                    definition_of_defined_concept = axiom1.getSuperClass();
                                    axiomDefinition = axiom1;
                                    break;
                                }else if (owlClass.equals(axiom1.getSuperClass())) {
                                    definition_of_defined_concept = axiom1.getSubClass();
                                    axiomDefinition = axiom1;
                                    break;
                                }
                            }
                        }
                    }
                }
                if (axiomDefinition == null){ // todo
                    random_after_type1--;
                    continue;
                }
                axiomSet.remove(axiomDefinition);
                List<Formula> formulas = ct.AxiomConverter_rightAnd(axiomSet);


                Formula definition = ct.ClassExpressionConverter(definition_of_defined_concept);
                List<Formula> ans = new ArrayList<>();
                if (definition != null) {
                    for (Formula f : formulas) {
                        Formula temp = inf.AckermannReplace(ct.getConceptfromClass(owlClass), f, definition);
                        if(!TautologyChecker.isTautology(temp)) ans.add(temp);
                    }
                }
                Set<OWLAxiom> replaced_axioms = bc.toOWLAxioms(ans);
                for (OWLAxiom axiom : replaced_axioms) {
                    Set<OWLClass> classes = axiom.getClassesInSignature();
                    for (OWLClass c1 : classes) {
                        if (map.getOrDefault(c1, null) == null) {
                            map.put(c1, new HashSet<>());
                        }
                        map.get(c1).add((OWLLogicalAxiom) axiom);
                    }
                    axioms.add((OWLLogicalAxiom) axiom);

                }
            }
            //再计算type2，这里偷懒了没有让他去删除
            int addTotype4 = 0;
            for(OWLClass owlClass : random_type2Set){
                Set<OWLLogicalAxiom> axiomSet = map.get(owlClass);
                axiomSet.removeAll(deletedAxioms);
                if(axiomSet.size() == 0){
                    random_after_type2--;
                }else {
                    for (OWLLogicalAxiom axiom : axiomSet) {
                        if (axiom instanceof OWLSubClassOfAxiom) {
                            if (((OWLSubClassOfAxiom) axiom).getSubClass().toString().contains(owlClass.toString())) {
                                if (!(((OWLSubClassOfAxiom) axiom).getSubClass() instanceof OWLClass)) {
                                    random_after_type2--;
                                    addTotype4++;
                                    // System.out.println(owlClass);
                                    // System.out.println(axiom);
                                    break;
                                }

                            }
                        }
                    }
                }
            }
            //再计算random_after_type4
            OWLOntologyManager manager3 = OWLManager.createOWLOntologyManager();
            OWLOntology ontoAfter = manager3.createOntology();
            for(OWLAxiom axiom : axioms)
                manager3.applyChange(new AddAxiom(ontoAfter, axiom));
            Set<OWLClass> classesAfter = ontoAfter.getClassesInSignature();
            classesAfter.removeAll(random_type1Set);
            classesAfter.removeAll(random_type2Set);
            classesAfter.removeAll(random_type3Set);
            random_after_type4 = Sets.intersection(random_type4Set,classesAfter).size()+addTotype4;
            int all_random_after_type = random_after_type1+random_after_type2+random_after_type3+random_after_type4;
            String nowLog3 ="3 "+ pathO1+","+pathO2 +" " + all_random_after_type+" "+
                    random_after_type1+" " + random_after_type2 +" "+ random_after_type3 + " "+random_after_type4;
            System.out.println(nowLog);
            System.out.println(nowLog2);
            System.out.println(nowLog3);

            writeFile.writeFile(dictPath + filelog, nowLog + "\n");
            writeFile.writeFile(dictPath + filelog, nowLog2 + "\n");
            writeFile.writeFile(dictPath + filelog, nowLog3 + "\n");

            System.out.println();





        }


    }


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
                            throw new Exception();
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



    public static void main(String[] args)throws Exception{

        testUI("Oxford-ISG","PARTI",0.3);
      //  testUI("Oxford-ISG","PARTIII",0.3);
      //  testUI("BioPortal","PARTII",0.3);
        testUI("BioPortal","PARTI",0.3);

        //AAAIJustify();
        //testDefinedConceptsNums();
        //testAAAI22();
        //staticalAAAI22();
        //testUI("PARTII",0.3);

        //testGhadah();
        //relationships();
        //statisticsBio();

        ///String[][] s1 = new String[][]{{"ontology_201601","ontology_201607"},{"ontology_201601","ontology_201701"},/*{"ontology_201601","ontology_201801"},*/
        //        {"ontology_201607","ontology_201701"},/*{"ontology_201701","ontology_201801"},{"ontology_201707","ontology_201801"},*/{"ontology_201901","ontology_201907"}
        ////        ,{"ontology_201607","ontology_201601"},{"ontology_201701","ontology_201601"},{"ontology_201701","ontology_201607"},{"ontology_201707","ontology_201701"}
        //        ,{"ontology_201801","ontology_201701"},{"ontology_201801","ontology_201707"},{"ontology_201807","ontology_201801"},{"ontology_201901","ontology_201801"}
        //        ,{"ontology_201901","ontology_201807"},{"ontology_201907","ontology_201901"},{"ontology_202007","ontology_202003"}};
//        System.out.println(s1.length);
       // String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/";
        //String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/TestData/Corpus_2/";
        //String dictPath = "/Users/liuzhao/nju/NCBO/data/Part_Ⅵ/";
       // for(String[] s : s1){
       //     List<OWLOntology>ans = test3(dictPath,s[0],s[1]);

      //  }
       // OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201707.owl"));
      //  OWLOntology onto2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201801.owl"));
        //OWLOntology ui = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"0170701801.owl"));
        //OWLOntology witness = checkWitness(ans.get(0),ans.get(1),ans.get(2),"/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/log.txt",
        //        "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/20011907");
        //test2(dictPath);
        //test4("corpus2");
        //List<OWLOntology>ans = test3(dictPath,"ontology_202001.owl","ontology_201907.owl");
        //OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201707.owl"));
        //OWLOntology onto2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(dictPath+"ontology_201801.owl"));
        //OWLOntology witness = checkWitness(ans.get(0),ans.get(1),ans.get(2),"/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/log.txt",
        //        "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/20011907");
        //System.out.println("done!");
    }


}

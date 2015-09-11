package com.el.dg;

import de.tudresden.inf.lat.jcel.coreontology.axiom.*;
import de.tudresden.inf.lat.jcel.owlapi.main.JcelReasoner;
import de.tudresden.inf.lat.jcel.owlapi.translator.TranslationRepository;
import de.tudresden.inf.lat.jcel.reasoner.main.RuleBasedReasoner;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import utils.LOG;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.nio.channels.NonReadableChannelException;
import java.nio.channels.SelectableChannel;
import java.sql.*;
import java.util.*;

/**
 * Created by winter on 28/8/15.
 */
public class PatternGeneration {
    private Set<NormalizedIntegerAxiom> tbox;
    private Set<NormalizedIntegerAxiom> tboxCP;
    private OWLOntology ontology;

    private Set<Set<NormalizedIntegerAxiom>> S;
    private Set<Set<NormalizedIntegerAxiom>> S_v;
    private Set<Set<NormalizedIntegerAxiom>> S_a;

    private Map<Set<NormalizedIntegerAxiom>, Integer> supportMap;
    private Map<Integer, OWLClass> classMap;
    private Map<Integer, OWLObjectProperty> propMap;

    private Map<Set<Set<NormalizedIntegerAxiom>>, PatternInfo> infoMap;

    private NormalizedIntegerAxiomFactoryImpl fat;

    public static final String url = "jdbc:mysql://localhost/test1";
    public static final String user = "root";
    public static final String password = "1";
    public static final String driver = "com.mysql.jdbc.Driver";

    final private static String TEMP_FILE = "temp.txt";

    private Connection dbConnection;

    final public static Map<String, Integer> axiomTypeMap = new HashMap<String, Integer>(){{
            put(GCI0Axiom.class.toString(), 1);
            put(GCI1Axiom.class.toString(), 2);
            put(GCI2Axiom.class.toString(), 3);
            put(GCI3Axiom.class.toString(), 4);
            put(RI2Axiom.class.toString(), 5);
            put(RI3Axiom.class.toString(), 6);
    }};

    final public static List<String> columnName = new ArrayList<String>(){{
        add("fnode");
        add("tnode");
        add(null);
        add("fir_node");
        add("sec_node");
        add("third_node");
    }};

    public PatternGeneration(OWLOntology ont) throws SQLException, ClassNotFoundException {
        Class.forName(driver);
        dbConnection = DriverManager.getConnection(url, user, password);
        dbConnection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
        Statement stmt = dbConnection.createStatement();
        stmt.execute("set session read_buffer_size=41943040"); // 40M
        stmt.execute("set session read_rnd_buffer_size=41943040"); // 40M
        stmt.execute("set session sort_buffer_size=167772160"); // 160M
        stmt.execute("set session join_buffer_size=167772160"); // 160M
        stmt.close();
        if (!dbConnection.getAutoCommit())
            dbConnection.commit();

        ontology = ont;

    }

    public void doGenerate() throws FileNotFoundException, SQLException, ClassNotFoundException {
        doPretreatment();
        //if (true) return;
        /* Pattern generation algorithm begin */
        Set<NormalizedIntegerAxiom> diffPattern = a_patternInSetDifference(S_a, S_v);

        while (diffPattern != null){
            Set<NormalizedIntegerAxiom> g = diffPattern;
            /* TBD */
            //S_a.remove(g);

            addPattern(S_v, g, false);

            if (findSubstitution(g, false)>0){
            	flushPattern(g, S.size());
                addPattern(S, g, false);
            }


            if (findSubstitution(g, true)>0){
                addPattern(S_a, g, true);

//                Iterator<NormalizedIntegerAxiom> gIterator = g.iterator();
//
//                while (gIterator.hasNext()){
//                    NormalizedIntegerAxiom axiom = gIterator.next();

                Set<Set<NormalizedIntegerAxiom>> candidatePattern = getCandidatePattern(g);

                Iterator<Set<NormalizedIntegerAxiom>> candiIterator = candidatePattern.iterator();

                while (candiIterator.hasNext())
                    addPattern(S_a, candiIterator.next(), true);

            }


            diffPattern = a_patternInSetDifference(S_a, S_v);
        }
    }
    
    /* save pattern immediately */
    private void flushPattern(Set<NormalizedIntegerAxiom> g, int patternId) throws SQLException, FileNotFoundException{
    	Statement stmt = dbConnection.createStatement();
    	
    	PrintStream out = new PrintStream(TEMP_FILE);

    	Integer support = supportMap.get(g);
    	
    	Iterator<NormalizedIntegerAxiom> patternIt = g.iterator();
        while (patternIt.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = patternIt.next();

            if (tmpAxiom instanceof GCI0Axiom){
                GCI0Axiom axiom = (GCI0Axiom) tmpAxiom;
                out.println(patternId + "\t" + axiomTypeMap.get(GCI0Axiom.class.toString())
                        + "\t" + axiom.getSubClass() + "\t"
                        + axiom.getSuperClass() + "\t0\t"
                        + support);
            }else if (tmpAxiom instanceof GCI1Axiom){
                GCI1Axiom axiom = (GCI1Axiom) tmpAxiom;
                out.println(patternId + "\t" + axiomTypeMap.get(GCI1Axiom.class.toString())
                        + "\t" + axiom.getLeftSubClass() + "\t"
                        + axiom.getRightSubClass() + "\t"
                        + axiom.getSuperClass() + "\t"
                        + support);
            }else if (tmpAxiom instanceof GCI2Axiom){
                GCI2Axiom axiom = (GCI2Axiom) tmpAxiom;
                out.println(patternId + "\t" + axiomTypeMap.get(GCI2Axiom.class.toString())
                        + "\t" + axiom.getSubClass() + "\t"
                        + axiom.getPropertyInSuperClass() + "\t"
                        + axiom.getClassInSuperClass() + "\t"
                        + support);
            }else if (tmpAxiom instanceof GCI3Axiom){
                GCI3Axiom axiom = (GCI3Axiom) tmpAxiom;
                out.println(patternId + "\t" + axiomTypeMap.get(GCI3Axiom.class.toString())
                        + "\t" + axiom.getPropertyInSubClass() + "\t"
                        + axiom.getClassInSubClass() + "\t"
                        + axiom.getSuperClass() + "\t"
                        + support);
            }else if (tmpAxiom instanceof RI2Axiom){
                RI2Axiom axiom = (RI2Axiom) tmpAxiom;
                out.println(patternId + "\t" + axiomTypeMap.get(RI2Axiom.class.toString())
                        + "\t" + axiom.getSubProperty() + "\t"
                        + axiom.getSuperProperty() + "\t"
                        + support);
            }else if (tmpAxiom instanceof RI3Axiom){
                RI3Axiom axiom = (RI3Axiom) tmpAxiom;
                out.println(patternId + "\t" + axiomTypeMap.get(RI3Axiom.class.toString())
                        + "\t" + axiom.getLeftSubProperty() + "\t"
                        + axiom.getRightSubProperty() + "\t"
                        + axiom.getSuperProperty() + "\t"
                        + support);
            }
        }
    	
		stmt.close();
		(new File(TEMP_FILE)).delete();
    }
    
    private void addISubstitution(Set<Set<NormalizedIntegerAxiom>> Sa, Set<NormalizedIntegerAxiom> pattern){
        Set<Integer> classSigSet = getClassSignature(pattern);
        Set<Integer> propertySet = getPropertySignature(pattern);

        int maxId = getMaxId(getSignature(pattern));

        /***** (X,Y)-forbidden *******/
        classSigSet.remove(1);
        classSigSet.remove(2);

        ArrayList<Integer> classSigList = new ArrayList<Integer>(classSigSet);
        ArrayList<Integer> propertySigList = new ArrayList<Integer>(propertySet);

        int classLength = classSigList.size();
        int proprtyLength = propertySigList.size();

        int[] classFlag = new int[classLength];
        int[] propertyFlag = new int[proprtyLength];




        for (int ci=1; ci<classLength; ci++){

            for (int pi=1; pi<proprtyLength; pi++){
                if (pi + ci == 2) continue;

                if (ci!=1)
                    for (int i=0; i<ci; i++) classFlag[i] = 1;

                if (pi!=1)
                    for (int i=0; i<pi; i++) propertyFlag[i] = 1;

                boolean classHasNext = true;
                while (classHasNext){
                    Set<Integer> classSubsSet = new HashSet<Integer>();
                    Set<Integer> propertySubsSet = new HashSet<Integer>();

                    boolean propertyHasNext = true;

                    while (propertyHasNext){

                        for (int i=0; i<classFlag.length; i++){
                            if (classFlag[i] == 1)
                                classSubsSet.add(classSigList.get(i));

                        }

                        for (int i=0; i<propertyFlag.length; i++){
                            if (propertyFlag[i] == 1)
                                propertySubsSet.add(propertySigList.get(i));
                        }

                        addSubsPattern(Sa, pattern, classSubsSet, propertySubsSet, maxId);

                        propertyHasNext = swapArray(propertyFlag);
                    }

                    classHasNext = swapArray(classFlag);
                }

            }
        }
    }

    private void addSubsPattern(Set<Set<NormalizedIntegerAxiom>> Sa, Set<NormalizedIntegerAxiom> pattern,
                                Set<Integer> classSubsSet, Set<Integer> proprtySubsSet, int maxID){
        Set<NormalizedIntegerAxiom> newPattern = new HashSet<NormalizedIntegerAxiom>();

        Map<Integer, Integer> newMap = new HashMap<Integer, Integer>();

        Set<Integer> classSigSet = getClassSignature(pattern);
        Set<Integer> propertySigSet = getPropertySignature(pattern);

        Iterator<Integer> classSetIt = classSigSet.iterator();
        while (classSetIt.hasNext()){
            Integer tmp = classSetIt.next();

            if (classSubsSet.contains(tmp)) newMap.put(tmp, maxID+1);
            else newMap.put(tmp, tmp);
        }

        Iterator<Integer> propertySetIt = propertySigSet.iterator();
        while (propertySetIt.hasNext()){
            Integer tmp = propertySetIt.next();

            if (proprtySubsSet.contains(tmp)) newMap.put(tmp, maxID+2);
            else newMap.put(tmp, tmp);
        }


        Iterator<NormalizedIntegerAxiom> patternIt = pattern.iterator();
        Set<String> axiomStringSet = new HashSet<String>();

        while (patternIt.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = patternIt.next();

            Set<Integer> classSet = tmpAxiom.getClassesInSignature();
            Set<Integer> propertySet = tmpAxiom.getObjectPropertiesInSignature();

            if (!containsOneOf(classSet, classSubsSet) && !containsOneOf(propertySet, proprtySubsSet)){
                newPattern.add(tmpAxiom);
            }else{

                if (tmpAxiom instanceof GCI0Axiom){
                    GCI0Axiom axiom = (GCI0Axiom) tmpAxiom;
                    Integer sub = newMap.get(axiom.getSubClass());
                    Integer sup = newMap.get(axiom.getSuperClass());

                    if (sub == sup) continue;

                    GCI0Axiom newAxiom = fat.createGCI0Axiom(sub, sup);

                    if (axiomStringSet.contains(newAxiom.toString())) continue;

                    newPattern.add(newAxiom);
                    axiomStringSet.add(newAxiom.toString());

                }else if (tmpAxiom instanceof GCI1Axiom){
                    GCI1Axiom axiom = (GCI1Axiom) tmpAxiom;
                    Integer leftSub = newMap.get(axiom.getLeftSubClass());
                    Integer rightSub = newMap.get(axiom.getRightSubClass());
                    Integer sup = newMap.get(axiom.getSuperClass());

                    GCI1Axiom newAxiom = fat.createGCI1Axiom(leftSub, rightSub, sup);

                    if (axiomStringSet.contains(newAxiom.toString())) continue;

                    newPattern.add(newAxiom);
                }else if (tmpAxiom instanceof GCI2Axiom){
                    GCI2Axiom axiom = (GCI2Axiom) tmpAxiom;
                    Integer sub = newMap.get(axiom.getSubClass());
                    Integer classInSup = newMap.get(axiom.getClassInSuperClass());
                    Integer propertyInSup = newMap.get(axiom.getPropertyInSuperClass());

                    GCI2Axiom newAxiom = fat.createGCI2Axiom(sub, propertyInSup, classInSup);

                    if (axiomStringSet.contains(newAxiom.toString())) continue;

                    newPattern.add(newAxiom);
                }else if (tmpAxiom instanceof GCI3Axiom){
                    GCI3Axiom axiom = (GCI3Axiom) tmpAxiom;
                    Integer classInSub = axiom.getClassInSubClass();
                    Integer proprtyInSub = axiom.getPropertyInSubClass();
                    Integer classInSup = axiom.getSuperClass();

                    GCI3Axiom newAxiom = fat.createGCI3Axiom(proprtyInSub, classInSub, classInSup);

                    if (axiomStringSet.contains(newAxiom.toString())) continue;

                    newPattern.add(newAxiom);
                }else if (tmpAxiom instanceof RI2Axiom){
                    RI2Axiom axiom = (RI2Axiom) tmpAxiom;
                    Integer proprtySub = axiom.getSubProperty();
                    Integer propertySup = axiom.getSuperProperty();

                    RI2Axiom newAxiom = fat.createRI2Axiom(proprtySub, propertySup);

                    if (axiomStringSet.contains(newAxiom.toString())) continue;
                    newPattern.add(newAxiom);
                }else if (tmpAxiom instanceof RI3Axiom){
                    RI3Axiom axiom = (RI3Axiom) tmpAxiom;
                    Integer leftProprtySub = axiom.getLeftSubProperty();
                    Integer rightPropertySub = axiom.getRightSubProperty();
                    Integer propertySup = axiom.getSuperProperty();

                    RI3Axiom newAxiom = fat.createRI3Axiom(leftProprtySub, rightPropertySub, propertySup);

                    if (axiomStringSet.contains(newAxiom.toString())) continue;

                    newPattern.add(newAxiom);
                }
            }
        }

        //cleanPattern(newPattern);
        addPattern(Sa, newPattern, true);
    }

    /* TBD */
    private void cleanPattern(Set<NormalizedIntegerAxiom> pattern){

    }

    private boolean containsOneOf(Set<Integer> baba, Set<Integer> erzi){
        Iterator<Integer> iterator = erzi.iterator();

        while (iterator.hasNext()){
            Integer tmp = iterator.next();

            if (baba.contains(tmp)) return true;
        }

        return false;
    }

    private boolean swapArray(int[] flagArray){
        int len = flagArray.length;

        for (int i=0; i<len-1; i++){
            if (flagArray[i]==1 && flagArray[i+1]==0){
                flagArray[i] = 0;
                flagArray[i+1] = 1;
                return true;
            }
        }

        return false;
    }

    private Set<Integer> getClassSignature(Set<NormalizedIntegerAxiom> pattern){
        Set<Integer> classSignature = new HashSet<Integer>();

        Iterator<NormalizedIntegerAxiom> iterator = pattern.iterator();
        while (iterator.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = iterator.next();
            classSignature.addAll(tmpAxiom.getClassesInSignature());
        }

        return classSignature;
    }

    private Set<Integer> getPropertySignature(Set<NormalizedIntegerAxiom> pattern){
        Set<Integer> propertySignature = new HashSet<Integer>();
        Iterator<NormalizedIntegerAxiom> iterator = pattern.iterator();
        while (iterator.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = iterator.next();
            propertySignature.addAll(tmpAxiom.getObjectPropertiesInSignature());
        }

        return propertySignature;
    }

    private Set<Integer> getSignature(Set<NormalizedIntegerAxiom> pattern){
        Set<Integer> signature = new HashSet<Integer>();

        Iterator<NormalizedIntegerAxiom> iterator = pattern.iterator();
        while (iterator.hasNext()){
            NormalizedIntegerAxiom axiom = iterator.next();

            signature.addAll(axiom.getClassesInSignature());
            signature.addAll(axiom.getObjectPropertiesInSignature());
        }
        return signature;
    }

    private Integer getMaxId(Set<Integer> idCollection){
        Iterator<Integer> iterator = idCollection.iterator();
        Integer res = 0;

        while (iterator.hasNext()){
            Integer id = iterator.next();

            if (id > res)
                res = id;
        }

        return res;
    }

    private Set<Set<NormalizedIntegerAxiom>> getCandidatePattern(Set<NormalizedIntegerAxiom> gSet){
        Set<Integer> signature = getSignature(gSet);
        Iterator<Integer> integerIterator = signature.iterator();
        int max = 0;
        while (integerIterator.hasNext()){
            Integer tmp = integerIterator.next();

            if (tmp > max)
                max = tmp;
        }

        Set<Set<NormalizedIntegerAxiom>> candidateSet = new HashSet<Set<NormalizedIntegerAxiom>>();
        Iterator<NormalizedIntegerAxiom> nit = gSet.iterator();

        while (nit.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = nit.next();

            Integer axiomType = PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString());

            if (axiomType != PatternGeneration.axiomTypeMap.get(GCI0Axiom.class.toString())
                    && axiomType != PatternGeneration.axiomTypeMap.get(GCI2Axiom.class.toString()))
                continue;
            else{
                Set<Set<NormalizedIntegerAxiom>> bodyPart = getRuleBody(tmpAxiom, max);

                Iterator<Set<NormalizedIntegerAxiom>> bodyPartIt = bodyPart.iterator();
                while (bodyPartIt.hasNext()){
                    Set<NormalizedIntegerAxiom> replacePart = bodyPartIt.next();

                    Set<NormalizedIntegerAxiom> replaceAxiomSet = new HashSet<NormalizedIntegerAxiom>();
                    replaceAxiomSet.addAll(gSet);
                    replaceAxiomSet.remove(tmpAxiom);
                    replaceAxiomSet.addAll(replacePart);

                    candidateSet.add(replaceAxiomSet);
                }
            }


        }

        return candidateSet;
    }

    /* replace rule.head with rule.body */
    private Set<Set<NormalizedIntegerAxiom>> getRuleBody(NormalizedIntegerAxiom axiom,  int maxId){

        Set<Set<NormalizedIntegerAxiom>> bodyPart = new HashSet<Set<NormalizedIntegerAxiom>>();

        if (axiom instanceof GCI0Axiom){
            GCI0Axiom tmpAxiom = (GCI0Axiom) axiom;

            Set<NormalizedIntegerAxiom> cp1 = new HashSet<NormalizedIntegerAxiom>();
            cp1.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId+1));
            cp1.add(fat.createGCI0Axiom(maxId+1, tmpAxiom.getSuperClass()));
            bodyPart.add(cp1);

            Set<NormalizedIntegerAxiom> cp2 = new HashSet<NormalizedIntegerAxiom>();
            cp2.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId+1));
            cp2.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId + 2));
            cp2.add(fat.createGCI1Axiom(maxId + 1, maxId + 2, tmpAxiom.getSuperClass()));
            bodyPart.add(cp2);

            Set<NormalizedIntegerAxiom> cp3 = new HashSet<NormalizedIntegerAxiom>();
            cp3.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId + 1));
            cp3.add(fat.createGCI1Axiom(tmpAxiom.getSubClass(), maxId + 1, tmpAxiom.getSuperClass()));
            bodyPart.add(cp3);

            Set<NormalizedIntegerAxiom> cp4 = new HashSet<NormalizedIntegerAxiom>();
            cp4.add(fat.createGCI0Axiom(tmpAxiom.getSubClass(), maxId + 1));
            cp4.add(fat.createGCI1Axiom(maxId + 1, tmpAxiom.getSubClass(), tmpAxiom.getSuperClass()));
            bodyPart.add(cp4);

            Set<NormalizedIntegerAxiom> cp5 = new HashSet<NormalizedIntegerAxiom>();
            cp5.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId + 1, maxId + 2));
            cp5.add(fat.createGCI0Axiom(maxId + 2, maxId + 3));
            cp5.add(fat.createGCI3Axiom(maxId + 1, maxId + 3, tmpAxiom.getSuperClass()));
            bodyPart.add(cp5);

            Set<NormalizedIntegerAxiom> cp6 = new HashSet<NormalizedIntegerAxiom>();
            cp6.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId+1, maxId+2));
            cp6.add(fat.createGCI3Axiom(maxId+1, maxId+2, tmpAxiom.getSuperClass()));
            bodyPart.add(cp6);

        }else{
            GCI2Axiom tmpAxiom = (GCI2Axiom) axiom;

            Set<NormalizedIntegerAxiom> cp7 = new HashSet<NormalizedIntegerAxiom>();
            cp7.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId + 1, tmpAxiom.getClassInSuperClass()));
            cp7.add(fat.createRI2Axiom(maxId + 1, tmpAxiom.getPropertyInSuperClass()));
            bodyPart.add(cp7);

            Set<NormalizedIntegerAxiom> cp8 = new HashSet<NormalizedIntegerAxiom>();
            cp8.add(fat.createGCI2Axiom(tmpAxiom.getSubClass(), maxId+1, maxId+2));
            cp8.add(fat.createGCI2Axiom(maxId+2, maxId+3, tmpAxiom.getClassInSuperClass()));
            cp8.add(fat.createRI3Axiom(maxId + 1, maxId + 3, tmpAxiom.getPropertyInSuperClass()));
            bodyPart.add(cp8);

        }

        return bodyPart;
    }

    private void addPattern(Set<Set<NormalizedIntegerAxiom>> patternSet, Set<NormalizedIntegerAxiom> pattern, boolean checkVariant){
        if (!checkVariant){
            patternSet.add(pattern);
            return;
        }

        Iterator<Set<NormalizedIntegerAxiom>> psIt = patternSet.iterator();
        while (psIt.hasNext()){
            Set<NormalizedIntegerAxiom> tmpPattern = psIt.next();
            if (isPatternEqual(tmpPattern, pattern))
                return;
        }

        patternSet.add(pattern);
    }

    /* normalize and get class, property map*/

    private void doPretreatment() throws FileNotFoundException, SQLException, ClassNotFoundException {
        JcelReasoner reasoner = new JcelReasoner(ontology, false);
        RuleBasedReasoner ruleBasedReasoner = (RuleBasedReasoner) reasoner.getReasoner();

        TranslationRepository translatorReposity = reasoner.getTranslator().getTranslationRepository();
        classMap = translatorReposity.getClassMap();
        propMap = translatorReposity.getObjectPropertyMap();

        LOG.info("Normalizing tbox...");
        tbox = ruleBasedReasoner.getNormalizedIntegerAxiomSet();
        LOG.info("completely.\n");

        fat  = new NormalizedIntegerAxiomFactoryImpl();

        S = new HashSet<Set<NormalizedIntegerAxiom>>();
        S_v = new HashSet<Set<NormalizedIntegerAxiom>>();
        S_a = new HashSet<Set<NormalizedIntegerAxiom>>();

        Set<NormalizedIntegerAxiom> initialPattern = new HashSet<NormalizedIntegerAxiom>();
        GCI0Axiom initialAxiom = fat.createGCI0Axiom(1, 2);
        //ruleBasedReasoner.isEntailed(initialAxiom);
        initialPattern.add(initialAxiom);
        S_a.add(initialPattern);

        supportMap = new HashMap<Set<NormalizedIntegerAxiom>, Integer>();

        TBoxCP tcp = new TBoxCP(dbConnection, tbox);
        tcp.generate();
        
        Statement stmt = dbConnection.createStatement();
        String ptable = "(patternId int not null, " +
                        "axiomType int not null, " +
                        "fir_node int not null, " +
                        "sec_node int not null, " +
                        "third_node int not null, " +
                        "support int not null)" ;

        stmt.execute("drop table if exists patterns");
        stmt.execute("create table patterns" + ptable);

        if (!dbConnection.getAutoCommit())
            dbConnection.commit();
        stmt.close();
    }

    public Set<NormalizedIntegerAxiom> a_patternInSetDifference(Set<Set<NormalizedIntegerAxiom>> Sa, Set<Set<NormalizedIntegerAxiom>> Sv){
        Iterator<Set<NormalizedIntegerAxiom>> saIt = Sa.iterator();

        while (saIt.hasNext()){
            Set<NormalizedIntegerAxiom> tmpSaPat = saIt.next();

            Iterator<Set<NormalizedIntegerAxiom>> svIt = Sv.iterator();
            boolean flag = true;

            while (svIt.hasNext()){
                Set<NormalizedIntegerAxiom> tmpSvPat = svIt.next();

                if (isPatternEqual(tmpSaPat, tmpSvPat)) {
                    flag = false;
                    break;
                }
            }

            if (flag){
                return tmpSaPat;
            }
        }

        return null;
    }

    private int findSubstitution(Set<NormalizedIntegerAxiom> g, boolean isTboxCp) throws SQLException {
        Statement stmt = dbConnection.createStatement();
        SQLInfo sqlinfo = compseSQL(g, isTboxCp);
        Map<String, ArrayList<Integer>> ineqMap = sqlinfo.ineqMap;

        ResultSet rt = stmt.executeQuery(sqlinfo.sql);

        int counter = 0;
        int fakeRow = 0;

        while (rt.next()){

            Iterator<String> iterator = ineqMap.keySet().iterator();
            while (iterator.hasNext()){
                String key = iterator.next();

                ArrayList<Integer> integerArrayList = ineqMap.get(key);
                Set<Integer> indexSet = new HashSet<Integer>();

                for (Integer index: integerArrayList){
                    if (indexSet.contains(index)){
                        fakeRow++;
                        break;
                    }else {
                        indexSet.add(index);
                    }
                }

            }
            counter++;
        }

        int support = counter - fakeRow;


        if (support>0){
            LOG.info(g.toString());
            LOG.info(sqlinfo.sql);
            LOG.info(support + "\n");
        }
        stmt.close();

        if (!isTboxCp && !supportMap.keySet().contains(g) && support!=0)
            supportMap.put(g, support);

        return support;
    }

    public Set<Set<NormalizedIntegerAxiom>> getPatterns(){
        return S;
    }

    private boolean isPatternEqual(Set<NormalizedIntegerAxiom> pa, Set<NormalizedIntegerAxiom> pb){

        //if (pa == pb) return true;

        if (pa.size() != pb.size())
            return false;

        Set<Integer> paCPSignature = getSignature(pa);
        Set<Integer> pbCPSignature = getSignature(pb);

        if (paCPSignature.size() != pbCPSignature.size())
            return false;

        PatternInfo paInfo = getPatternInfo(pa);
        PatternInfo pbInfo = getPatternInfo(pb);

        return paInfo.isEqual(pbInfo);
    }

    private SQLInfo compseSQL(Set<NormalizedIntegerAxiom> pattern, boolean isTboxCp){
        if (pattern == null)
            return null;

        String sqlstmt = "select * from ";

        String tablePrefix = "p";
        if (!isTboxCp) tablePrefix = "t" + tablePrefix;

        Map<Integer, IDInfo> equalMap = new HashMap<Integer, IDInfo>();
        Iterator<NormalizedIntegerAxiom> axiomIterator = pattern.iterator();

        Integer index = 0;
        Map<String, ArrayList<Integer>> ineqMap = new HashMap<String, ArrayList<Integer>>();
        SQLInfo sqlInfo = new SQLInfo();

        while (axiomIterator.hasNext()){


            NormalizedIntegerAxiom tmpAxiom = axiomIterator.next();

            if (!ineqMap.keySet().contains(tmpAxiom.getClass().toString())){
                ArrayList<Integer> integerArrayList = new ArrayList<Integer>();
                integerArrayList.add(index);
                ineqMap.put(tmpAxiom.getClass().toString(), integerArrayList);
            }else{
                // Maybe a bug here
                ineqMap.get(tmpAxiom.getClass().toString()).add(index);
            }



            Integer[] iris = getIRIs(tmpAxiom);


            Integer axiomTypeInt = PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString());

            String tableStr = tablePrefix + axiomTypeInt;

            String tmpTableStr = "h" + index.toString();
            if (index == 0){
                sqlstmt += tableStr + " " + tmpTableStr + " ";
            }else {
                String joinStmt = "inner join ";
                sqlstmt += joinStmt + tableStr + " " + tmpTableStr;
            }
                Integer eqIndex = 0;
                for (int i = 0; i<iris.length; i++){
                    if (equalMap.keySet().contains(iris[i])){
                        if (eqIndex == 0) sqlstmt += " on ";
                        if (eqIndex != 0) sqlstmt += "and ";

                        IDInfo info = equalMap.get(iris[i]);
                        String eqLeft = "h" + info.index.toString() + "." + info.column + "=";

                        String eqRight = tmpTableStr + "." + PatternGeneration.columnName.get((iris.length-2)*3+i) + " ";

                        sqlstmt += eqLeft + eqRight + " ";

                        if (PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString())
                                == info.axiomType && index != info.index){
                            sqlstmt += "and " + "h" + index + ".id<>h" + info.index + ".id ";
                        }

                        eqIndex++;
                    }else{
                        /* store the first */
                        String columnName = PatternGeneration.columnName.get((iris.length - 2) * 3 + i);
                        Integer type = PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString());
                        equalMap.put(iris[i], new IDInfo(columnName, index, type));

                    }
                }

                if (eqIndex == 0)
                    sqlstmt += " ";



//            for (int i = 0; i<iris.length; i++){
//                if (!equalMap.keySet().contains(iris[i])){
//
//                    /* store the first */
//                    equalMap.put(iris[i], new IDInfo(PatternGeneration.columnName.get((iris.length-2)*3+i), index,
//                            PatternGeneration.axiomTypeMap.get(tmpAxiom.getClass().toString())));
//                }


            index++;
        }
        sqlInfo.ineqMap = ineqMap;
        sqlInfo.sql = sqlstmt;

        return sqlInfo;
    }

    private String getColumnName(Integer length, Integer index){
        return PatternGeneration.columnName.get((length-2)*3+index);
    }

    private PatternInfo getPatternInfo(Set<NormalizedIntegerAxiom> pattern){
        PatternInfo patternInfo = new PatternInfo();

        Iterator<NormalizedIntegerAxiom> patternIt = pattern.iterator();


        while (patternIt.hasNext()){
            NormalizedIntegerAxiom tmpAxiom = patternIt.next();

            String className = tmpAxiom.getClass().toString();
            if (patternInfo.axiomTypeCount.keySet().contains(className)){
                patternInfo.axiomTypeCount.put(className, patternInfo.axiomTypeCount.get(className)+1);
            }else{
                patternInfo.axiomTypeCount.put(className, 1);
            }

            if (patternInfo.iriCount.keySet().contains(className)){
                Set<Integer> tmpSet = new HashSet<Integer>();
                tmpSet.addAll(tmpAxiom.getClassesInSignature());
                tmpSet.addAll(tmpAxiom.getObjectPropertiesInSignature());
                tmpSet.addAll(patternInfo.iriCount.get(className));
                patternInfo.iriCount.put(className, tmpSet);
            }else{
                Set<Integer> tmpSet = new HashSet<Integer>();
                tmpSet.addAll(tmpAxiom.getClassesInSignature());
                tmpSet.addAll(tmpAxiom.getObjectPropertiesInSignature());
                patternInfo.iriCount.put(className, tmpSet);
            }
        }

        return patternInfo;
    }

    private Integer[] getIRIs(NormalizedIntegerAxiom axiom){
        if (axiom instanceof GCI0Axiom){
            GCI0Axiom tmpAxiom = (GCI0Axiom) axiom;
            Integer[] iris = new Integer[2];
            iris[0] = tmpAxiom.getSubClass();
            iris[1] = tmpAxiom.getSuperClass();
            return iris;
        }else if (axiom instanceof GCI1Axiom){
            GCI1Axiom tmpAxiom = (GCI1Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getLeftSubClass();
            iris[1] = tmpAxiom.getRightSubClass();
            iris[2] = tmpAxiom.getSuperClass();
            return iris;
        }else if (axiom instanceof GCI2Axiom){
            GCI2Axiom tmpAxiom = (GCI2Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getSubClass();
            iris[1] = tmpAxiom.getPropertyInSuperClass();
            iris[2] = tmpAxiom.getClassInSuperClass();
            return iris;
        }else if (axiom instanceof GCI3Axiom){
            GCI3Axiom tmpAxiom = (GCI3Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getPropertyInSubClass();
            iris[1] = tmpAxiom.getClassInSubClass();
            iris[2] = tmpAxiom.getSuperClass();
            return iris;
        }else if (axiom instanceof RI2Axiom){
            RI2Axiom tmpAxiom = (RI2Axiom) axiom;
            Integer[] iris = new Integer[2];
            iris[0] = tmpAxiom.getSubProperty();
            iris[1] = tmpAxiom.getSuperProperty();
            return iris;
        }else if (axiom instanceof RI3Axiom){
            RI3Axiom tmpAxiom = (RI3Axiom) axiom;
            Integer[] iris = new Integer[3];
            iris[0] = tmpAxiom.getLeftSubProperty();
            iris[1] = tmpAxiom.getRightSubProperty();
            iris[2] = tmpAxiom.getSuperProperty();
            return iris;
        }else{
            LOG.info("WTF! " + axiom.toString());
            return null;
        }

    }

    public void savePattern() throws SQLException, FileNotFoundException {
        Statement stmt = dbConnection.createStatement();
        String ptable = "(patternId int not null, " +
                        "axiomType int not null, " +
                        "fir_node int not null, " +
                        "sec_node int not null, " +
                        "third_node int not null, " +
                        "support int not null)" ;

        stmt.execute("drop table if exists patterns");
        stmt.execute("create table patterns" + ptable);

        if (!dbConnection.getAutoCommit())
            dbConnection.commit();

        PrintStream out = new PrintStream(TEMP_FILE);

        Integer patternId = 1;

        Iterator<Set<NormalizedIntegerAxiom>> sIterator = S.iterator();
        while (sIterator.hasNext()){
            Set<NormalizedIntegerAxiom> pattern = sIterator.next();
            Integer support = supportMap.get(pattern);

            Iterator<NormalizedIntegerAxiom> patternIt = pattern.iterator();
            while (patternIt.hasNext()){
                NormalizedIntegerAxiom tmpAxiom = patternIt.next();

                if (tmpAxiom instanceof GCI0Axiom){
                    GCI0Axiom axiom = (GCI0Axiom) tmpAxiom;
                    out.println(patternId + "\t" + axiomTypeMap.get(GCI0Axiom.class.toString())
                            + "\t" + axiom.getSubClass() + "\t"
                            + axiom.getSuperClass() + "\t0\t"
                            + support);
                }else if (tmpAxiom instanceof GCI1Axiom){
                    GCI1Axiom axiom = (GCI1Axiom) tmpAxiom;
                    out.println(patternId + "\t" + axiomTypeMap.get(GCI1Axiom.class.toString())
                            + "\t" + axiom.getLeftSubClass() + "\t"
                            + axiom.getRightSubClass() + "\t"
                            + axiom.getSuperClass() + "\t"
                            + support);
                }else if (tmpAxiom instanceof GCI2Axiom){
                    GCI2Axiom axiom = (GCI2Axiom) tmpAxiom;
                    out.println(patternId + "\t" + axiomTypeMap.get(GCI2Axiom.class.toString())
                            + "\t" + axiom.getSubClass() + "\t"
                            + axiom.getPropertyInSuperClass() + "\t"
                            + axiom.getClassInSuperClass() + "\t"
                            + support);
                }else if (tmpAxiom instanceof GCI3Axiom){
                    GCI3Axiom axiom = (GCI3Axiom) tmpAxiom;
                    out.println(patternId + "\t" + axiomTypeMap.get(GCI3Axiom.class.toString())
                            + "\t" + axiom.getPropertyInSubClass() + "\t"
                            + axiom.getClassInSubClass() + "\t"
                            + axiom.getSuperClass() + "\t"
                            + support);
                }else if (tmpAxiom instanceof RI2Axiom){
                    RI2Axiom axiom = (RI2Axiom) tmpAxiom;
                    out.println(patternId + "\t" + axiomTypeMap.get(RI2Axiom.class.toString())
                            + "\t" + axiom.getSubProperty() + "\t"
                            + axiom.getSuperProperty() + "\t"
                            + support);
                }else if (tmpAxiom instanceof RI3Axiom){
                    RI3Axiom axiom = (RI3Axiom) tmpAxiom;
                    out.println(patternId + "\t" + axiomTypeMap.get(RI3Axiom.class.toString())
                            + "\t" + axiom.getLeftSubProperty() + "\t"
                            + axiom.getRightSubProperty() + "\t"
                            + axiom.getSuperProperty() + "\t"
                            + support);
                }
            }
            patternId++;

        }

        out.close();
        stmt.execute("load data local infile '" + TEMP_FILE + "' ignore into table patterns");
        if (!dbConnection.getAutoCommit())
            dbConnection.commit();

        stmt.close();
        (new File(TEMP_FILE)).delete();

    }

    public Set<Set<NormalizedIntegerAxiom>> restorePattern(){
        //TODO
        return null;
    }
}
 class IDInfo{
     public String column;
     public Integer index;
     public Integer axiomType;

     public IDInfo(String col, Integer idx, Integer type){
         column = col;
         index = idx;
         axiomType = type;
     }
 };

class SQLInfo{
    public String sql;
    public Map<String, ArrayList<Integer>> ineqMap;
}


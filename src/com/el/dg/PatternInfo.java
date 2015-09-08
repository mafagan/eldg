package com.el.dg;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Created by winter on 29/8/15.
 */
public class PatternInfo {
    public Map<String, Integer> axiomTypeCount;
    public Map<String, Set<Integer>> iriCount;

    public PatternInfo(){
        axiomTypeCount = new HashMap<String, Integer>();
        iriCount = new HashMap<String, Set<Integer>>();
    }

    public boolean isEqual(PatternInfo b){
        if (axiomTypeCount.keySet().size() != b.axiomTypeCount.keySet().size())
            return false;

        Iterator<String> atcIt = axiomTypeCount.keySet().iterator();

        while (atcIt.hasNext()){
            String key = atcIt.next();

            if (!axiomTypeCount.get(key).equals(b.axiomTypeCount.get(key)))
                return false;
        }

        Iterator<String> iriKeyIt = iriCount.keySet().iterator();

        while (iriKeyIt.hasNext()){
            String key = iriKeyIt.next();

            Set<Integer> axiomTypeIDCount = iriCount.get(key);
            Set<Integer> pbAxiomTypeCount = b.iriCount.get(key);

            if (!axiomTypeIDCount.equals(pbAxiomTypeCount))
                return false;

        }


        //TODO find substitution
        return true;
    }
}

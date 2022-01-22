package Test.Test;

import org.junit.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class aliTest {
    public static Map<String,Integer> cache = new HashMap<>();

    @Test
    public void test(){

        String str = "ccdaabcdbb";
        String[] strs = new String[]{"ab","cd"};

        int ans = helper(str,strs);
        System.out.println(ans);
    }
    public int helper(String str, String[] canRemovedStrs){
        if(str == null || str.length() == 0){
            return 0;
        }
        if(cache.containsKey(str)) return cache.get(str);
        int ans = str.length();
        System.out.println(str);
        for(String canRemovedStr : canRemovedStrs){
            if(canRemovedStr.length()> str.length()) continue;//剪枝
            if(canRemovedStr.length() == 0) continue;
            int fromPos = 0;
            while(fromPos != -1 && fromPos < canRemovedStr.length()){
                int index = str.indexOf(canRemovedStr,fromPos);
                if(index == -1) break;
                String temp = str.substring(0,index) + str.substring(index+canRemovedStr.length(),str.length());
                int tempans = helper(temp,canRemovedStrs);
                ans = Math.min(ans,tempans);
                fromPos = index+1;

            }
        }
        cache.put(str,ans);
        return ans;
    }
    /*
    public int helper(String str, String[] canRemovedStrs){
        if(cache.containsKey(str)) return cache.get(str);
        if(str == null || str.length() == 0){
            return 0;
        }
        int ans = str.length();
        System.out.println(str);
        for(String canRemovedStr : canRemovedStrs){
            if(canRemovedStr.length()> str.length()) continue;//剪枝
            if(canRemovedStr.length() == 0) continue;
            //先求kmp的match回退数组
            int[] match = new int[canRemovedStr.length()];
            match[0] = -1;
            for(int i = 1; i < canRemovedStr.length() ; i++){
                int j = match[i-1];
                while(j >= 0 && str.charAt(i) != str.charAt(j+1)) j = match[j];
                if(j < 0) match[i] = -1;
                else match[i] = j+1;
            }

            List<Integer> matchPos = new ArrayList<>();//记录匹配的点
            //开始进行匹配，寻求匹配的点
            int i =0, j = 0;
            while(i < str.length()){
                if(str.charAt(i) == canRemovedStr.charAt(j)){
                    i++;
                    j++;
                    if(j == canRemovedStr.length()){
                        matchPos.add(i-canRemovedStr.length());
                        j=0;
                    }
                }
                else if(j == 0)i++;
                else j = match[j-1]+1;
            }
            //进行dfs
            for(Integer pos : matchPos){
                String temp = str.substring(0,pos)+str.substring(pos+canRemovedStr.length(),str.length());
                int tempans = helper(temp,canRemovedStrs);
                ans = Math.min(ans,tempans);
            }
        }
        cache.put(str,ans);
        return ans;
    }

     */
    @Test
    public void test2(){
        int n = 5;
        int[][] connects = new int[][]{{1,2},{5,1},{2,3},{4,2}};
        int q = 12;
        int [][] queries = new int[][]{{1,1},{2,3},{3,1},{3,2},{3,3},{3,4},{1,2},{2,4},{3,1},{3,3},{3,4},{3,5}};
        List<Integer> ans = helper(n,connects,q,queries);
        for(Integer a : ans) System.out.println(a);
    }
    public List<Integer> helper(int n, int[][] connects, int q, int[][] queries){
        Map<Integer,Integer> father = new HashMap<>();// 1,2 就表示2的father是1
        Map<Integer,List<Integer>> children = new HashMap<>(); // 1 3， 1 2 表示 1的children是【2，3】
        Map<Integer,Integer> states = new HashMap<>(); // 每个蓄水池的状态 初始为空
        // 初始化 father children
        for(int[] connect : connects ){
            if(connect[0] > connect[1]){
                int temp = connect[0];
                connect[0] = connect[1];
                connect[1] = temp;
            }
            father.put(connect[1],connect[0]);
            List<Integer> now = children.getOrDefault(connect[0],new ArrayList<>());
            now.add(connect[1]);
            children.put(connect[0],now);
        }
        List<Integer> ans = new ArrayList<>();
        for(int[] query : queries){
            if(query[0] == 1){
                fillPoll(query[1],states,children);
            }else if(query[0] == 2){
                clearPool(query[1],states,father);
            }else if(query[0] == 3){
                ans.add(states.getOrDefault(query[1],0));
            }
        }
        return ans;



    }
    public void fillPoll(int pool,Map<Integer,Integer> states,Map<Integer,List<Integer>> children){
        states.put(pool,1);
        List<Integer> child = children.get(pool);
        if(child != null && child.size() != 0){
            for(Integer i : child){
                fillPoll(i,states,children);
            }
        }
    }
    public void clearPool(int pool, Map<Integer,Integer> states, Map<Integer,Integer> father){
        states.put(pool,0);
        if(father.containsKey(pool)){
            clearPool(father.get(pool),states,father);
        }
    }

}

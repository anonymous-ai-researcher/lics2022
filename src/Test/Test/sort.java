package Test.Test;

import org.junit.Test;

import java.util.HashMap;

public class sort {
    @Test
    public void test(){
        int[] nums = new int[]{3,4,51,7,1,13,6,1,0,-1,4,3,21,4,56,42,5};
        QuickSort(nums,0,nums.length-1);
        for(int i : nums) System.out.print(i+" ");
        System.out.println();
    }
    public void QuickSort(int[] nums, int left, int right){
        if(left >= right) return;

        int pivot = partition(nums,left, right);
        QuickSort(nums,left, pivot-1);

        QuickSort(nums,pivot+1, right);

    }
    private int partition(int[] nums, int left, int right){
        int pivot = nums[left];
        int p = left+1;
        for(int i = left+1 ; i <= right ; i++){
            if(nums[i] <= pivot){
                int temp = nums[p];
                nums[p] = nums[i];
                nums[i]  =temp;
                p++;
            }
        }
        int temp = nums[left];
        nums[left] = nums[p-1];
        nums[p-1] = temp;

        return p-1;
    }
}

package forgetting;

public class saveMetrics {
    public int optimizeNum1;
    public int optimizeNum2;
    public int optimizeNum3;
    public int optimizeNum4;
    public double optimizeTime;
    public int isExtra;
    public int success;
    public saveMetrics(){
        optimizeNum1 = -1;
        optimizeNum2 = -1;
        optimizeNum3 = -1;
        optimizeNum4 = -1;
        optimizeTime = -1;
        isExtra = 0;
        success = 0;
    }
    public String returnMetrics(){
        return optimizeNum1 +","+optimizeNum2+","+optimizeNum3+","+optimizeNum4+","+optimizeTime;
    }


}

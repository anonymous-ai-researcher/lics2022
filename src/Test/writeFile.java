package Test;

import java.io.FileWriter;
import java.io.IOException;

public class writeFile {
    public static void writeFile(String path,String  ans){
        try {
            FileWriter writer = new FileWriter(path,true);
            //int Line = 0;
            writer.write(ans);

            writer.close();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
    public static  void main(String [] args){
        writeFile("/Users/liuzhao/Desktop/www.txt","111\n");
        writeFile("/Users/liuzhao/Desktop/www.txt","222\n");

    }
}

package Test;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class readFile {
    public static ArrayList<String> readFile(String path){
        ArrayList<String> arrayList = new ArrayList<>();
        try {
            File file = new File(path);
            InputStreamReader input = new InputStreamReader(new FileInputStream(file));
            BufferedReader bf = new BufferedReader(input);
            // 按行读取字符串
            String str;
            while ((str = bf.readLine()) != null) {
                arrayList.add(str);
            }
            bf.close();
            input.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return arrayList;
    }
}

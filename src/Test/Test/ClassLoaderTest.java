package Test.Test;

import java.io.*;
import java.sql.Driver;
import java.sql.DriverManager;
import java.util.Enumeration;
import java.util.Properties;
import java.util.WeakHashMap;

public class ClassLoaderTest extends ClassLoader{

    private String classLoaderName;
    private String baseUrl;

    //自定义findClass方法，只有在使用自定义累加器时，才会调用
    @Override
    public Class<?> findClass(String className){
        System.out.println("自定义findClass被调用...");
        String path = baseUrl + className.replace(".", "/") + ".class";
        System.out.println("当前加载的类的全限定名是 ：" + path);
        byte data[] = findData(path);
        Class<?> calzz = defineClass(className, data, 0, data.length);
        return calzz;
    }


    @Override
    protected Class<?> loadClass(String className, boolean resolve) throws ClassNotFoundException {
        if(className.startsWith("apiForPy.showData")){
            System.out.println("666");
            return this.findClass(className);
        }
        System.out.println("777");
        System.out.println(className);
        return super.loadClass(className, resolve);

    }

    public ClassLoaderTest(String calssLoader) {
        super();
        this.classLoaderName = calssLoader;
    }

    public ClassLoaderTest(ClassLoader parent, String calssLoader) {
        super(parent);
        this.classLoaderName = calssLoader;
    }

    //设置一个路径，用来存放编译生成的.class文件；
    //该路径与默认的classPath不同，AppClassLoader无法加载该路径下的类，自定义类加载器可以加载该路径下的类
    private void setPath(String baseUrl) {
        this.baseUrl = baseUrl;
    }

    //自定义findData 将.class文件解析成byte数组
    private byte[] findData(String className) {
        InputStream in = null;
        byte[] ch = null;
        ByteArrayOutputStream out = null;

        try {
            in = new FileInputStream(new File(className));
            out = new ByteArrayOutputStream();
            int a = 0;
            while( -1 != (a = in.read())) {
                out.write(a);
            }
            ch = out.toByteArray();
            return ch;
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }finally {
            try {
                out.close();
                in.close();
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        return ch;
    }


    public static void main(String[] args) throws Exception {

        System.out.println("-----");
        Enumeration<Driver>en =  DriverManager.getDrivers();
        while(en.hasMoreElements()){
            Driver d = en.nextElement();
            System.out.println(d.toString());
        }
        ClassLoaderTest loader1 = new ClassLoaderTest("loader1");
        loader1.setPath("/Users/liuzhao/Desktop/");//设置自定义类加载器的加载路径
        //被类加载器加载后，得到Class对象
        Class<?> c1 = loader1.loadClass("apiForPy.showData");
        Object o1 = c1.newInstance();//实例化MyTest1
        System.out.println();

        ClassLoaderTest loader2 = new ClassLoaderTest("loader1");
        loader2.setPath("/Users/liuzhao/Desktop/");
        Class<?> c2 = loader2.loadClass("BackTrack.BackTrack");
        Object o2 = c2.newInstance();
        System.out.println(o1.getClass().getClassLoader());
        System.out.println(o2.getClass().getClassLoader());
        System.out.println(System.getProperty("jdbc.drivers"));
        Properties properties = System.getProperties();
        System.out.println(c1.getClassLoader());


    }
}

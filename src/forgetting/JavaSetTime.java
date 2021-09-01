package forgetting;

import java.util.concurrent.*;

public class JavaSetTime {

    public static void main(String[] args) {
        Callable<String> task = new Callable<String>() {
            @Override
            public String call() throws Exception {
                //设置执行响应时间的方法体
                String str = JavaSetTime.sleepJavaTest();
                System.err.println("打印str"+str);
                return str;
            }
        };
        ExecutorService exeservices = Executors.newSingleThreadExecutor();
        Future<String> future = exeservices.submit(task);
        try {
            String result = future.get(5, TimeUnit.SECONDS);
            System.err.println("打印result"+result);
        } catch (TimeoutException e) {
            e.printStackTrace();
            //异常处理的方法
            System.err.println("5秒钟没有执行完毕！这里是异常处理的方法");
            System.exit(0);

        }catch (InterruptedException e2){
            System.err.println("52秒钟没有执行完毕！这里是异常处理的方法");
        }
        catch (ExecutionException e3){
            System.err.println("53秒钟没有执行完毕！这里是异常处理的方法");
        }
    }

    public static String sleepJavaTest() {

        try {
            /*java中sleep与wait的区别
             * 对于sleep方法导致程序暂停执行指定的时间，让出cpu给其他线程。但是它的监控状态依然保持，时间到了就会恢复。
             * 在sleep方法中，线程不会释放对象锁。
             * 对于wait方法，线程会放弃对象锁，进入等待次对象的等待锁定池，
             * 只有针对此对象调用notify()后，本线程才进入对象锁定池的准备。
             */
            Thread.sleep(6000);
            return "当前函数成功的返回";
        } catch (InterruptedException e) {
            e.printStackTrace();
            System.out.println("dddd");
            return "执行异常";
        }
    }

}
package Test.Test;

import connectives.Inclusion;
import org.junit.Test;

import java.util.concurrent.Callable;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public class interruptTry {
    @Test
    public  void test0() throws Exception{
        try {
            Thread thread = Thread.currentThread();
            Callable<Integer> task = new Callable<Integer>() {
                @Override
                public Integer call() {
                    try {
                        thread.interrupt();
                        // 取消定时器任务
                    } catch (Exception e) {
                    }
                    return 1;
                }
            };
            ScheduledThreadPoolExecutor executor = new ScheduledThreadPoolExecutor(1);

            ScheduledFuture<?> f = executor.schedule(
                    task, 1000, TimeUnit.MILLISECONDS);
            f.get();
            while (true){
                System.out.println(333);
            }
        }catch (InterruptedException e){
            System.out.println("fgggggg");
        }
    }
    @Test
    public void test1() throws Exception{
        Thread thread = new Thread(new Runnable() {
            @Override
            public void run() {
                int i = 0;
                while(true){
                    System.out.println(i++);
                }
            }
        });
        thread.start();
        thread.join(500);
        thread.stop();
        int i =0;
        while (i > 2006968){
            i++;
        }
    }
}

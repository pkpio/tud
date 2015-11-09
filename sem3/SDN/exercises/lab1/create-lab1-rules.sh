#cleanup
dpctl del-flows tcp:127.0.0.1:6634

#SMTP filters - Task 2
dpctl add-flow tcp:127.0.0.1:6634 tcp,tp_src=25,idle_timeout=0,actions=
dpctl add-flow tcp:127.0.0.1:6634 tcp,tp_dst=25,idle_timeout=0,actions=

#Port mapping - Task 1
dpctl add-flow tcp:127.0.0.1:6634 dl_dst=00:00:00:00:00:01,idle_timeout=0,actions=output:1
dpctl add-flow tcp:127.0.0.1:6634 dl_dst=00:00:00:00:00:02,idle_timeout=0,actions=output:2
dpctl add-flow tcp:127.0.0.1:6634 dl_dst=00:00:00:00:00:03,idle_timeout=0,actions=output:3
dpctl add-flow tcp:127.0.0.1:6634 dl_dst=ff:ff:ff:ff:ff:ff,idle_timeout=0,actions=all

# redis
# appendonly
sudo vim /etc/redis/redis.conf
sudo sed -i 's/bind 127.0.0.1 -::1//g' /etc/redis/redis.conf
sudo service redis-server restart
echo "CONFIG SET protected-mode no" | redis-cli
echo "FLUSHALL" | redis-cli
# oha
oha -q 100 -z 10s --latency-correction --disable-keepalive --no-tui http://127.0.0.1:3000 
# wrk
./wrk2/wrk -t2 -c16 -d30s -R100 --latency http://127.0.0.1:3000
# htop
htop -p $(pgrep -d',' -f "hz-server")
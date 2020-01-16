port=34375
echo "Copying trafficIsolation package to VM on port" $port
scp -P $port -r ~/cs422/lab08_part2/trafficIsolation/ osboxes@localhost:~/

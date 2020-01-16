port=49643
echo "Copying trafficIsolation package from VM on port " $port
scp -P $port -r osboxes@localhost:~/trafficIsolation/ ~/cs422/lab08_part2/

#!/bin/bash

#Do not insert code here

#DO NOT REMOVE THE FOLLOWING TWO LINES
git add $0 >> .local.git.out
git commit -a -m "Lab 2 commit" >> .local.git.out
git push >> .local.git.out || echo

# cycles per second
hertz=$(getconf CLK_TCK)

function check_arguments {


	#If number of arguments is less than 5, exit. For part 2, the number of arguments should be greater than 7
	if [ "$1" -lt 7 ]; then
		echo "USAGE: "
		#echo "$0 {process id} -cpu {utilization percentage} {maximum reports} {time interval}"
		# Change the prompt to include mem montoring (for a small fee)
		echo "$0 {process id} -cpu {cpu usage percentage} -mem {maximum memory in kB} {maximum reports} {time interval}"
		exit
	fi

	CPU_THRESHOLD=$4

	#Extract the memory threshold (part 2 of the script)
	MEM_THRESHOLD=$6

}

function init
{

	#Remove reports directory
	rm -fr ./reports_dir
	mkdir ./reports_dir

	REPORTS_DIR=./reports_dir

	PID=$1 #This is the pid we are going to monitor

	TIME_INTERVAL=${@:$#} #Time interval is the last argument

	MAXIMUM_REPORTS=${@:$#-1:1} #Maximum reports is the argument before the last

}

#This function calculates the CPU usage percentage given the clock ticks in the last $TIME_INTERVAL seconds
function jiffies_to_percentage {
	
	#Get the function arguments (oldstime, oldutime, newstime, newutime)
	oldstime=$1
	oldutime=$2
	newstime=$3
	newutime=$4
	#Calculate the elpased ticks between newstime and oldstime (diff_stime), and newutime and oldutime (diff_stime)
	diff_stime=$((newstime - oldstime))
	diff_utime=$((newutime - oldutime))
	
	#You will use the following command to calculate the CPU usage percentage. $TIME_INTERVAL is the user-provided time_interval
	#Note how we are using the "bc" command to perform floating point division

	echo "100 * ( ($diff_stime + $diff_utime) / $hertz) / $TIME_INTERVAL" | bc -l
}


#This function takes as arguments the cpu usage and the memory usage that were last computed
function generate_report {

	
	#if ./reports_dir has more than $MAXIMUM_REPORTS reports, then, delete the oldest report to have room for the current one
	oldest=""
	count=0
	#Loop through the contents of the reports directory, and find the oldest file, also count the amount of files in the directory
	for file in "./reports_dir/"/*; do
		[[ -z $oldest || $file -ot $oldest ]] && oldest=$file
		count=$((count+1))
	done
	# If there's too many files in the directory, kill the oldest
	if [ $count -eq $MAXIMUM_REPORTS ]; then
		#echo "Removing: "$oldest  >&2
		rm $oldest
	fi
	
	#Name of the report file
	file_name="$(date +'%d.%m.%Y.%H.%M.%S')"

	#Extracting process name from /proc
	process_name=$(cat /proc/$PID/stat | awk '{print $2}')

	#You may uncomment the following lines to generate the report. Make sure the first argument to this function is the CPU usage
	#and the second argument is the memory usage

	#Write the report info the file, BUT DON"T RETURN IT
	echo "PROCESS ID: $PID" > ./reports_dir/$file_name
	echo "PROCESS NAME: $process_name" >> ./reports_dir/$file_name
	echo "CPU USAGE: $1 %" >> ./reports_dir/$file_name
	echo "MEMORY USAGE: $2 kB" >> ./reports_dir/$file_name
	
	#Now return the filepath so that notify() can use it to be lazy and sent the email
	echo "./reports_dir/"$file_name
}

#Returns a percentage representing the CPU usage
function calculate_cpu_usage {

	#echo "calculate cpu"  >&2
	#CPU usage is measured over a periode of time. We will use the user-provided interval_time value to calculate 
	#the CPU usage for the last interval_time seconds. For example, if interval_time is 5 seconds, then, CPU usage
	#is measured over the last 5 seconds
	if [ -e "/proc/$PID" ]; then
		#First, get the current utime and stime (oldutime and oldstime) from /proc/{pid}/stat
		#the result of cat is piped into awk which returns the 14th or 15th word
		oldutime=$(cat /proc/$PID/stat | awk '{print $14}')
		oldstime=$(cat /proc/$PID/stat | awk '{print $15}')

		#Sleep for time_interval
		#echo "sleeping for "$TIME_INTERVAL >&2
		sleep $TIME_INTERVAL
		
		if [[ ! -e "/proc/$PID" ]]; then
			#echo "quitting from inside CPU" >&2
			exit
		fi

		#Now, get the current utime and stime (newutime and newstime) /proc/{pid}/stat
		#Column 14 is utime, 15 is stime
		newutime=$(cat /proc/$PID/stat | awk '{print $14}')
		newstime=$(cat /proc/$PID/stat | awk '{print $15}')
		
		#The values we got so far are all in jiffier (not Hertz), we need to convert them to percentages, we will use the function
		#jiffies_to_percentage

		percentage=$(jiffies_to_percentage $oldutime $oldstime $newutime $newstime)


		#Return the usage percentage
		echo "$percentage" #return the CPU usage percentage
	else
		#echo "not exist" >&2 #Testy for testing things
		#If the process is no longer, then we shouldn't bother other people, like usual, and return nothing
		echo ""
	fi

	
}

function calculate_mem_usage
{
	#echo "calculate mem"  >&2
	if [ -e "/proc/$PID" ]; then
		#Let us extract the VmRSS value from /proc/{pid}/status
		mem_usage=$(cat /proc/$PID/status | awk '{if ($1 == "VmRSS:") print $2}')
		#awk '{if ($1 == "VmRSS:") print $2}'
		
		#Return the memory usage
		echo "$mem_usage"
	else
		#if the process is no longer running, then our life is meaningless and we should return nothing
		echo ""
	fi	
}
#Takes the report file as a third argument -- for lazi-- efficiency 
function notify
{
	#We convert the float representating the CPU usage to an integer for convenience. We will compare $usage_int to $CPU_THRESHOLD
	cpu_usage_int=$(printf "%.f" $1)

	#Check if the process has exceeded the thresholds

	#Check if process exceeded its CPU or MEM thresholds. If that is the case, send an email to $USER containing the last report
	if [ $cpu_usage_int -gt $CPU_THRESHOLD ] || [ $2 -gt $MEM_THRESHOLD ]; then
		# $3 is the filePath to the report file, read that into the mail body and send it to the USER (RIP my mailbox)
		cat $3 | mail -s "Threshold violation for $PID" $USER
	fi
}


check_arguments $# $@

init $1 $@

# echo "Arguments"
# echo "#0:" $0
# echo "#1:" $1
# echo "#2:" $2
# echo "#3:" $3
# echo "#4:" $4
# echo "#5:" $5
# echo "#6:" $6
# echo "#7:" $7
# echo "#8:" $8

echo "CPU THRESHOLD: $CPU_THRESHOLD"
echo "MEM THRESHOLD: $MEM_THRESHOLD"
echo "MAXIMUM REPORTS: $MAXIMUM_REPORTS"
echo "Time interval: $TIME_INTERVAL" 

#The monitor runs forever
#while [ -n "$(ls /proc/$PID)" ] #While this process is alive BROKEN

#if the process is running, then there exists an info file in /proc/
# Checking if it's there, allows the program to not execute when the PID is not executing
while [ -e "/proc/$PID" ] #While this process is alive
do
	#part 1
	cpu_usage=$(calculate_cpu_usage)
	#part 2
	mem_usage=$(calculate_mem_usage)
	
	if [ -e "/proc/$PID" ]; then
		#If the script has started during the time that the PID has died, then we need to recheck whether the PID is still running
		#Else our cpu and mem info is useless
	
		report=$(generate_report $cpu_usage $mem_usage)
		#Call the notify function to send an email to $USER if the thresholds were exceeded
		#notify $cpu_usage $mem_usage
		notify $cpu_usage $mem_usage $report
	else
		# if the process is no longer running, kill ourselves
		exit
	fi

done

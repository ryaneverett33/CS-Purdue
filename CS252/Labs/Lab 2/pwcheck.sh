#!/bin/bash

#DO NOT REMOVE THE FOLLOWING TWO LINES
git add $0 >> .local.git.out
git commit -a -m "Lab 2 commit" >> .local.git.out
git push >> .local.git.out || echo


#Your code here
#read from passwordfile ($1)
if [ ! -e $1 ]; then
	#continue
	echo "File doesn't exist!"
	exit
fi

pass=$(cat $1)
length=${#pass}
if [ $length -lt 6 -o $length -gt 32 ]; then
	echo "Error: Password length invalid."
	exit
#else
#	#echo "proper length"
fi

score=$length

#Special characters regex: [\$\#\+\%\@] +5
#One alpha character: [A-Za-z] +5
#Contains a number: [0-9] +5
special=$(egrep [\$\#\+\%\@] $1)
alpha=$(egrep [A-Za-z] $1)
conNumber=$(egrep [0-9] $1)
if [ "${#special}" -gt 0 ]; then
	#echo "has special characters:" $special
	score=$(($score+5))
#else
	#echo "does not contain special"
fi
if [ "${#alpha}" -gt 0 ]; then
	#echo "has an alpha character:" $alpha
	score=$(($score+5))
#else
	#echo "does not contain alpha"
fi
if [ "${#conNumber}" -gt 0 ]; then
	#echo "contains a number:" $conNumber
	score=$(($score+5))
#else
	#echo "does not contain a number"
fi
#https://stackoverflow.com/a/10552175/2220534 for loops

lastchar=0
count=0
lowCount=0
upCount=0
numCount=0
repeatAlpha=false
repeatUpper=false
repeatLower=false
repeatNum=false
charType=0			#0-Special, 1-Character, 2-digit
for (( i=0; i<${#pass}; i++ )); do
	curr=${pass:$i:1}
	#echo $curr
	if [[ $curr =~ [a-z] ]]; then
		charType=1
	elif [[ $curr =~ [A-Z] ]]; then
		charType=1
	elif [[ $curr =~ [0-9] ]]; then
		charType=2	
	else
		charType=0	
	fi

	#if [ "$i" -eq 0 ]; then
	#	lastchar=$curr
	#	echo $lastchar
	#	continue
	#fi
	
	if [ $curr == $lastchar ] && [ $charType -ne 0 ]; then
		count=$((count+1))
		#echo "Matches, count="$count
		if [ $repeatAlpha == false ]; then
			score=$((score-10))
			repeatAlpha=true
			#echo "Repeating characters (-10)"
		fi
	else
		count=0
	fi
	if [[ $curr =~ [A-Z] ]] && [ $repeatUpper == false ]; then
		upCount=$((upCount+1))
		if [ "$upCount" -eq "3" ]; then
			score=$((score-3))
			repeatUper=true
			#echo "-3 for repeating Upper"
		fi
	else
		upCount=0
	fi
	if [[ $curr =~ [a-z] ]] && [ $repeatLower == false ]; then
		lowCount=$((lowCount+1))
		if [ "$lowCount" -eq "3" ]; then
			score=$((score-3))
			repeatLower=true		
			#echo "-3 for repeating lower"
		fi
	else
		lowCount=0
	fi
	if [ $charType -eq 2 ] && [ $repeatNum == false ]; then
		numCount=$((numCount+1))
		if [ "$numCount" -eq "3" ]; then
			score=$((score-3))
			repeatNum=true
			#echo "Consective numbers (-3)"
		fi
	else
		#echo "curr:$curr, lastchar:$lastchar, charType:$charType, count=$count"
		numCount=0
	fi
	lastchar=$curr
done
echo "Password Score:" $score

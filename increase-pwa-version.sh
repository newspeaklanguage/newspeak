#
# Replaces the version line in service worked JS file sw.js
# This could be a one-liner if we could assume GNU tools are installed.
#

SW_FILE=platforms/webIDE/sw.js

if [ ! -f ${SW_FILE} ]; then
    echo Service worker file does not exist, returning
    # Note: only can do this if this is sourced!
    return
fi

# Pull the version number from code. Assumes a fixed syntax for it.
PWA_VERSION=$(sed -E -n "s/^const pwaVersion = ([0-9]+);$/\1/p" ${SW_FILE})

# Increase the version number
PWA_VERSION=$((${PWA_VERSION} + 1))

# If backup file exists, store it under a different name, just in case
if [ -f ${SW_FILE}.bu ]; then echo Moving an old backup, just in case ...; mv ${SW_FILE}.bu ${SW_FILE}.bu.old; fi

# Replace the version number in code for the increased version.
sed -E -i.bu "s/^const pwaVersion = ([0-9]+);$/const pwaVersion = ${PWA_VERSION};/" ${SW_FILE}

# Lazy check the substitution did not trash the file - must differ by max 1 char. If not, go to .bu
SIZE_DIFF=$(( $(wc ${SW_FILE} | awk '{print $3}') - $(wc ${SW_FILE}.bu | awk '{print $3}') )) 
if [ ${SIZE_DIFF} -gt 1 -o ${SIZE_DIFF} -lt 0 ]; then
    echo ERROR sed likely failed to substitute, going back to backup. SIZE_DIFF=$SIZE_DIFF  
    mv ${SW_FILE}.bu ${SW_FILE}
else
    echo
    echo increase-pwa-version.sh : Success: Increased the PWA version in ${SW_FILE} to pwaVersion=${PWA_VERSION}. SIZE_DIFF=$SIZE_DIFF
    echo increase-pwa-version.sh : Removing the backup file ${SW_FILE}.bu
    echo
    rm ${SW_FILE}.bu
fi

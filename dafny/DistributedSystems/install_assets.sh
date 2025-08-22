# split -b 80M -d -a 1 dotnet-sdk-6.0.319-linux-x64.tar.gz dotnet-sdk-6.0.319-linux-x64.tar.gz.
cat ./assets/dotnet-sdk-6.0.319-linux-x64.tar.gz.* | tar -zxv

tar -zxvf ./assets/dafny3-42.tar.gz

chmod +x dotnet-sdk-6.0.319-linux-x64/
chmod +x dafny3.4/



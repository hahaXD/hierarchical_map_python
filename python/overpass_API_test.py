import requests
from optparse import OptionParser

left =  -118.537676
bottom = 34.015020
right = -118.404472 
top = 34.077037 

url  = "http://overpass-api.de/api/map?bbox={},{},{},{}".format(left, bottom, right, top)
parser = OptionParser()
parser.add_option("-o", "--osm", action="store", type="string", dest="filename")
parser.add_option("-l", "--left", action="store", type="float", dest="left")
parser.add_option("-b", "--bottom", action="store", type="float", dest="bottom")
parser.add_option("-r", "--right", action="store", type="float", dest="right")
parser.add_option("-t", "--top", action="store", type="float", dest="top")
(options, args) = parser.parse_args()
if options.left:
    left = options.left
if options.right:
    right = options.right
if options.bottom:
    bottom = options.bottom
if options.top:
    top = options.top
response = requests.get(url)
filename = options.filename
if(response.status_code == 400):
  print("Bad request. Bounding box may be too big.")
  print(response.text)
elif(response.status_code == 409):
  print("Too many requests")
else:
    with open(filename, 'wb') as handle:
        for block in response.iter_content(1024):
            handle.write(block)
  #print(response.status_code)
  #print(response.encoding)
  #print(response.text.encode('utf-8'))

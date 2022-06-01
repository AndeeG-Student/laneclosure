#!/usr/bin/env python
# coding: utf-8

import arcgis
from arcgis.gis import GIS
from arcgis.geoenrichment import *
import smtplib, ssl
import logging, re, os
import arcpy, shutil, sys
import xml.dom.minidom as DOM
from arcpy import env
import unicodedata
import datetime, tzlocal
from datetime import date, timedelta, datetime
from time import sleep
from time import strftime
import math, random
from os import listdir
from cmath import isnan
from math import trunc
from _server_admin.geometry import Point
import pandas as pd
from pandas.core.computation.ops import isnumeric
try:
    import urllib.request, urllib.error, urllib.parse  # Python 2
except ImportError:
    import urllib.request as urllib2  # Python 3
import urllib.request
import urllib.parse
import urllib.error
import http.client
import time
import contextlib
import zipfile
from zipfile import ZipFile
import json
import fileinput
from os.path import isdir, isfile, join
import matplotlib.pyplot as pyd
from IPython.display import display #, YouTubeVideo
from IPython.display import HTML
from arcgis.features._data.geodataset.geodataframe import SpatialDataFrame
from arcgis import geometry
from arcgis import features 
import arcgis.network as network
from arcgis.features.analyze_patterns import interpolate_points
import arcgis.geocoding as geocode
from arcgis.features.find_locations import trace_downstream
from arcgis.features.use_proximity import create_buffers
from arcgis.features import GeoAccessor as gac, GeoSeriesAccessor as gsac
from arcgis.features import SpatialDataFrame as spedf
from arcgis.features import FeatureLayer
import numpy as np
from copy import deepcopy
import sqlite3
from builtins import isinstance
from socrata import Socrata
from socrata.authorization import Authorization

#Searches for matching GIS data, returns the match if found, search for the Content Owner with "Owner_Value"
def webexsearch(mgis, title, owner_value, item_type_value, max_items_value=1000, inoutside=False):
    item_match = None
    search_result = mgis.content.search(query= "title:{} AND owner:{}".format(title, owner_value), 
                                          item_type = item_type_value, max_items=max_items_value, outside_org=inoutside)
    if "Imagery Layer" in item_type_value:
        item_type_value = item_type_value.replace("Imagery Layer", "Image Service")
    elif "Layer" in item_type_value:
        item_type_value = item_type_value.replace("Layer", "Service")
    
    for item in search_result:
        if item.title == title:
            item_match = item
            break
    return item_match

#Search Layers and return matching layer if found
def lyrsearch(lyrlist, lyrname):
    lyr_match = None
   
    for lyr in lyrlist:
        if lyr.properties.name == lyrname:
            lyr_match = lyr
            break
    return lyr_match

def create_section(lyr, hdrow, chdrows,rtefeat):
    try:
        object_id = 1
        pline = geometry.Polyline(rtefeat)
        feature = features.Feature(
            geometry=pline[0],
            attributes={
                'OBJECTID': object_id,
                'PARK_NAME': 'My Park',
                'TRL_NAME': 'Foobar Trail',
                'ELEV_FT': '5000'
            }
        )

        lyr.edit_features(adds=[feature])
        #_map.draw(point)

    except Exception as e:
        print("Couldn't create the feature. {}".format(str(e)))
        
#Creates a field object at a location and contains the fields below
def fldvartxt(fldnm,fldtyp,fldnull,fldPrc,fldScl,fldleng,fldalnm,fldreq):
    fld = arcpy.Field()
    fld.name = fldnm
    fld.type = fldtyp
    fld.isNullable = fldnull
    fld.precision = fldPrc
    fld.scale = fldScl
    fld.length = fldleng
    fld.aliasName = fldalnm
    fld.required = fldreq
    return fld

#Returns empty data frame with same col names and dtypes as df
def df_colsame(df):
    #df0 = pd.DataFrame.spatial({i[0]: pd.Series(dtype=i[1]) for i in df.dtypes.iteritems()}, columns=df.dtypes.index)
    return df

def offdirn(closide,dirn1):
    if closide == 'Right':
        offdirn1 = 'RIGHT'
    elif closide == 'Left':
        offdirn1 = 'LEFT'
        dirn1 = -1*dirn1
    elif closide == 'Center':
        offdirn1 = 'RIGHT'
        dirn1 = 0.5
    elif closide == 'Both':
        offdirn1 = 'RIGHT'
        dirn1 = 0
    elif closide == 'Directional':
        if dirn1 == -1:
            offdirn1 = 'LEFT'
        else:
            offdirn1 = 'RIGHT'
    elif closide == 'Full' or closide == 'All':
        offdirn1 = 'RIGHT'
        dirn1 = 0
    elif closide == 'Shift':
        offdirn1 = 'RIGHT'
    elif closide == 'Local':
        offdirn1 = 'RIGHT'
    else:
        offdirn1 = 'RIGHT'
        dirn1 = 0 
    return offdirn1,dirn1

def deleteupdates(prjstlyrsrc, sectfeats):
    for x in prjstlyrsrc:
        print (" layer: {} ; from item : {} ; URL : {} ; Container : {} ".format(x,x.fromitem,x.url,x.container))
        if 'Projects' in (prjstlyrsrc):
            xfeats =  x.query().features
            if len(xfeats) > 0:
                if isinstance(xfeats,(list,tuple)):
                    if "OBJECTID" in xfeats[0].attributes:
                        oids = "'" + "','".join(str(xfs.attributes['OBJECTID']) for xfs in xfeats if 'OBJECTID' in xfs.attributes ) + "'"
                        oidqry = " OBJECTID in ({}) ".format(oids)
                    elif "OID" in xfeats[0].attributes:    
                        oids = "'" + "','".join(str(xfs.attributes['OID']) for xfs in xfeats if 'OID' in xfs.attributes ) + "'"
                        oidqry = " OID in ({}) ".format(oids)
                    print (" from item : {} ; oids : {} ; ".format(x.fromitem,oids))
                    
                elif isinstance(xfeats,spedf):
                    if "OBJECTID" in xfeats.columns:
                        oids = "'" + "','".join(str(f1.get_value('OBJECTID')) for f1 in xfeats ) + "'"
                        oidqry = " OBJECTID in ({}) ".format(oids)
                    elif "OID" in xfeats.columns:    
                        oids = "'" + "','".join(str(f1.get_value('OID')) for f1 in xfeats ) + "'"
                        oidqry = " OID in ({}) ".format(oids)
                    print (" from item : {} ; oids : {} ; ".format(x.fromitem,oids))
                    
                if 'None' in oids:
                    print (" from item : {} ; oids : {} ; ".format(x.fromitem,oids))
                else:
                    x.delete_features(where=oidqry)

# Given anydate and n1 as 0 or 1 or 2 , etc  it computes Last Friday, First Friday and Second Friday, etc at 4PM
def fridaywk(bdate,n1):
    wkdte = datetime.strftime(bdate,"%w") # + datetime.strftime(bdate,"%z")
    date4pm = datetime.strptime(datetime.strftime(bdate,"%Y-%m-%d"),"%Y-%m-%d") + timedelta(hours=16)
    fr4pm= date4pm + timedelta(days=(5-int(wkdte)+(n1-1)*7))
    return fr4pm

def intextold(intxt,rte,rtename):
    intshortlbl = intxt['address']['ShortLabel']
    intsplitxt = intshortlbl.split(sep='&', maxsplit=1)
    txtret=intsplitxt[1]  # default to the second intersection unless the second one has the route
    for txt in intsplitxt:
        if rtename not in txt or rte not in txt:
            txtret = txt
    return txtret          

def intextshortlabel(intxt,rte,rtename,fromtxt="Nothing"):
    intshortlbl = intxt['address']['ShortLabel']
    rtext = re.sub("-","",rte)
    if rtename is None:
        rtenametxt = 'Nothing'
    else:    
        rtenametxt = re.sub("-","",rtename)
    intsplitxt = intshortlbl.split(sep='&') #, maxsplit=1)
    intsplitxt = [t1.strip() for t1 in intsplitxt ]
    if len(intsplitxt)==2: 
        txtret=intsplitxt[1]  # default to the second intersection unless the second one has the route
    elif len(intsplitxt)==3:
        txtret=intsplitxt[2]  # default to the second intersection unless the second one has the route
    else:
        txtret=intsplitxt[0]  # default to the second intersection unless the second one has the route
            
    rtenmsplit = [ t2.strip() for t2 in rtenametxt.split(sep=" ")]
    if len(rtenmsplit)>2:
        rtenmsplit = "{} {}".format(rtenmsplit[0].capitalize(),rtenmsplit[1].capitalize())
    else:
        rtenmsplit = "{}".format(rtenmsplit[0].capitalize())
               
    for txt in intsplitxt:
        txtsep = txt.split(sep=" ")
        if len(txtsep)<=2 :
            if (txt[0:2]).isnumeric():
                txt = "Exit " + txt.upper()
        if rtenmsplit not in txt and rtext not in txt and fromtxt!=txt:
            txtret = txt
        else:
            txtret = txt
    return txtret          

def intext(intxt,rte,rtename,fromtxt="Nothing"):
    txtmatchaddress = intxt['address']['Match_addr']  # ['ShortLabel']
    intshortlbl = txtmatchaddress.split(sep=',')[0]
    rtext = re.sub("-","",rte)
    if rtename is None:
        rtenametxt = 'Nothing'
    else:    
        rtenametxt = re.sub("-","",rtename)
    intsplitxt = intshortlbl.split(sep='&') #, maxsplit=1)
    intsplitxt = [t1.strip() for t1 in intsplitxt ]
    if len(intsplitxt)==2: 
        txtret=intsplitxt[1]  # default to the second intersection unless the second one has the route
    elif len(intsplitxt)==3:
        txtret=intsplitxt[2]  # default to the second intersection unless the second one has the route
    else:
        txtret=intsplitxt[0]  # default to the second intersection unless the second one has the route
            
    rtenmsplit = [ t2.strip() for t2 in rtenametxt.split(sep=" ")]
    if len(rtenmsplit)>2:
        rtenmsplit = "{} {}".format(rtenmsplit[0].capitalize(),rtenmsplit[1].capitalize())
    else:
        rtenmsplit = "{}".format(rtenmsplit[0].capitalize())
               
    for txt in intsplitxt:
        txtsep = txt.split(sep=" ")
        if len(txtsep) <= 2 :
            if (txt[0:2]).isnumeric():
                txt = "Exit " + txt.upper()
        if rtenmsplit not in txt and rtext not in txt and fromtxt != txt:
            txtret = txt
        else:
            txtret = txt
    return txtret        

def datemidnight(bdate):
    date0am = datetime.strptime(datetime.strftime(bdate,"%Y-%m-%d"),"%Y-%m-%d") + timedelta(hours=0)
    return date0am

def datemidnight(bdate,x=0):
    date0am = datetime.strptime(datetime.strftime(bdate,"%Y-%m-%d"),"%Y-%m-%d") + timedelta(hours=x)
    return date0am

#Returns whether or not closure date range is weekend or weekday
def wkend(b,e):
    if b==0 and e <=1: 
        return 1 
    elif b>=1 and b<=5 and e>=1 and e<= 5: 
        return 0 
    elif b>=5 and (e == 6 or e == 0): 
        return 1 
    else: 
        return 0
    
def beginwk(bdate):
    wkdte = datetime.strftime(bdate,"%w")
    if (wkdte==0):
        bw = bdate + timedelta(days=wkdte)
    else:  # wkdte>=1:
        bw = bdate + timedelta(days=(7-wkdte))
    return bw

def beginthiswk(bdate):
    wkdte = datetime.strftime(bdate,"%w")
    if (wkdte==0):
        bw = bdate - timedelta(days=wkdte)
    else:  # wkdte>=1:
        bw = bdate - timedelta(days=(8-int(wkdte)))
    return bw    

def midnextnight(bdate,n1):
    datenextam = datetime.strptime(datetime.strftime(bdate,"%Y-%m-%d"),"%Y-%m-%d") + timedelta(day=n1)
    return datenextam

#BeginDateName,EndDateName:  The month and the day portion of the begin or end date. (ex. November 23)
def dtemon(dte):
    dtext = datetime.strftime(dte-timedelta(hours=10),"%B") + " " +  str(int(datetime.strftime(dte-timedelta(hours=10),"%d")))
    return dtext

# BeginDay, EndDay: Weekday Name of the begin date (Monday, Tuesday, Wednesday, etc.)
def daytext(dte):
    dtext = datetime.strftime(dte-timedelta(hours=10),"%A") 
    return dtext

#BeginTime, EndTime: The time the lane closure begins.  12 hour format with A.M. or P.M. at the end
def hrtext(dte):
    hrtext = datetime.strftime(dte-timedelta(hours=10),"%I:%M %p") 
    return hrtext

def rtempt(lyrts,rtefc,lrte,bmpvalx,offs=0):
    if arcpy.Exists(mptbl):    
        if int(arcpy.GetCount_management(mptbl).getOutput(0)) > 0:
            arcpy.DeleteRows_management(mptbl)
    bmpval = bmpvalx
    rteFCSel = "RteSelected"
    rtevenTbl = "RteLinEvents"
    eveLinlyr = "lrtelyr" #os.path.join('in_memory','lrtelyr')
    arcpy.env.overwriteOutput = True
    if (len(rtefc)>0):
        flds = ['OBJECTID', 'SHAPE@JSON', 'ROUTE'] # selected fields in Route
        lrterows = arcpy.da.SearchCursor(lrte,flds)
        mpinscur.insertRow((rteid.upper(), bmpval,offs))
        dirnlbl = 'LEFT'
        arcpy.MakeRouteEventLayer_lr(lrte,fldrte,mptbl,eveProLines, eveLinlyr,ofFld.name,"ERROR_FIELD","ANGLE_FIELD",'NORMAL','ANGLE',dirnlbl)
        # get the geoemtry from the result layer and append to the section feature class
        if arcpy.Exists(eveLinlyr):    
            cntLyr = arcpy.GetCount_management(eveLinlyr)
        if cntLyr.outputCount > 0:
            #lrsectfldnms = [ f.name for f in arcpy.ListFields(eveLinlyr)]
            insecgeo = None
            # dynamic segementaiton result layer fields used to create the closure segment  
            lrsectfldnms = ['ObjectID', 'Route', 'BMP', 'Shape@JSON']
            evelincur = arcpy.da.SearchCursor(eveLinlyr,lrsectfldnms)
            for srow in evelincur:
                #insecgeo = srow.getValue("SHAPE@")
                #print("id : {} , Rte : {} , BMP {} , EMP : {} , Geom : {} ".format(srow[0],srow[1],srow[2],srow[3],srow[4]))
                rtenum = srow[1]
                insecgeo = arcgis.geometry.Geometry(srow[4])
                if insecgeo == None:
                    print('Not able to create section geometry for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,bmpval,empval,offs ))
                    logger.info('Not able to create section geometry for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,bmpval,empval,offs ))
                    insecgeo = geomrte.project_as(sprefwgs84)
                else:
                    print('created project section for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,bmpval,empval,offs ))
                    logger.info('created project section for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,bmpval,empval,offs ))
                insecgeo = insecgeo.project_as(sprefwgs84)
            del evelincur        
        del rteFCSel,lrte,rtevenTbl  
    else:
        rteidx = "460"  # Molokaii route 0 to 15.55 mileage
        print('Route {} not found using {} create section geometry layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(rteid,rteidx,lyrts,rteid,bmpvalx,bmpval,empval,offs ))
        logger.info('Route {} not found using {} to create section geometry layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(rteid,rteidx,lyrts,rteid,bmpvalx,bmpval,empval,offs ))
        featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteidx,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
        ftlnclrte = featlnclrte.features
        if (len(ftlnclrte)>0):
            rtegeo = ftlnclrte[0].geometry
            geomrte = arcgis.geometry.Geometry(rtegeo)
            insecgeo = geomrte.project_as(sprefwgs84)
        else:
            insecgeo=None    
    return insecgeo

def rtesectmpo(lyrts,rteid,bmpvalx,empvalx,offs):
    if arcpy.Exists(mptbl):    
        if int(arcpy.GetCount_management(mptbl).getOutput(0)) > 0:
            arcpy.DeleteRows_management(mptbl)
    bmpval = bmpvalx
    empval = empvalx
    rteFCSel = "RteSelected"
    rtevenTbl = "RteLinEvents"
    eveLinlyr = "lrtelyr" #os.path.join('in_memory','lrtelyr')
    arcpy.env.overwriteOutput = True
    featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteid,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
    if (len(featlnclrte)<=0):
        if rteid == "5600":
            rteid="560"
        else:
            rteid="560"    
        featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteid,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
    if (len(featlnclrte)>0):
        rteFCSel = featlnclrte.save('in_memory','rtesel')
        ftlnclrte = featlnclrte.features
        rtegeo = ftlnclrte[0].geometry
        geomrte = arcgis.geometry.Geometry(rtegeo,sr=sprefwebaux)
        rtepaths = rtegeo['paths']
        rtept1 = rtepaths[0][0] # geomrte.first_point
        rtept2 = rtepaths[0][len(rtepaths[0])-1] #geomrte.last_point
        bmprte = round(rtept1[2],3)
        emprte = round(rtept2[2],3)
        if (empval<bmpval):
            inpval = empval
            empval=bmpval
            bmpval = inpval
        elif (round(empval,3)==0 and bmpval<=0):
            empval=bmpval + 0.01
                
        if (bmpval<bmprte):
            bmpval=bmprte
        if (bmpval>emprte):
            bmpval=bmprte
        if (empval>emprte):
            empval=emprte
    
        #rteFCSel = featlnclrte.save(lcfgdboutpath,'rtesel')
        arcpy.env.outputMFlag = "Disabled"
        lrte = os.path.join('in_memory','rteselyr')
        arcpy.CreateRoutes_lr(rteFCSel,RteFld.name, lrte, "TWO_FIELDS", bmpFld.name, empFld.name)
        flds = ['OBJECTID', 'SHAPE@JSON', 'ROUTE'] # selected fields in Route
        lrterows = arcpy.da.SearchCursor(lrte,flds)
        
        if (abs(empval-bmpval)<0.01):
            bmpval=max(bmpval,empval)-0.005
            empval=bmpval+0.01
        mpinscur.insertRow((rteid.upper(), bmpval,empval,offs))
        dirnlbl = 'LEFT'
        arcpy.MakeRouteEventLayer_lr(lrte,fldrte,mptbl,eveProLines, eveLinlyr,ofFld.name,"ERROR_FIELD","ANGLE_FIELD",'NORMAL','ANGLE',dirnlbl)
        # get the geoemtry from the result layer and append to the section feature class
        if arcpy.Exists(eveLinlyr):    
            cntLyr = arcpy.GetCount_management(eveLinlyr)
        if cntLyr.outputCount > 0:
            #lrsectfldnms = [ f.name for f in arcpy.ListFields(eveLinlyr)]
            insecgeo = None
            # dynamic segementaiton result layer fields used to create the closure segment  
            lrsectfldnms = ['ObjectID', 'Route', 'BMP', 'EMP', 'Shape@JSON']
            evelincur = arcpy.da.SearchCursor(eveLinlyr,lrsectfldnms)
            for srow in evelincur:
                #insecgeo = srow.getValue("SHAPE@")
                #print("id : {} , Rte : {} , BMP {} , EMP : {} , Geom : {} ".format(srow[0],srow[1],srow[2],srow[3],srow[4]))
                rtenum = srow[1]
                insecgeo = arcgis.geometry.Geometry(srow[4])
                if insecgeo == None:
                    print('Not able to create section geometry for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                    logger.info('Not able to create section geometry for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                    insecgeo = geomrte.project_as(sprefwgs84)
                else:
                    print('created project section for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                    logger.info('created project section for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrts,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                insecgeo = insecgeo.project_as(sprefwgs84)
            del evelincur        
        del rteFCSel,lrte,rtevenTbl  
    else:
        rteidx = "460"  # Molokaii route 0 to 15.55 mileage
        print('Route {} not found using {} create section geometry layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(rteid,rteidx,lyrts,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
        logger.info('Route {} not found using {} to create section geometry layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(rteid,rteidx,lyrts,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
        featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteidx,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
        ftlnclrte = featlnclrte.features
        if (len(ftlnclrte)>0):
            rtegeo = ftlnclrte[0].geometry
            geomrte = arcgis.geometry.Geometry(rtegeo)
            insecgeo = geomrte.project_as(sprefwgs84)
        else:
            insecgeo=None    
    return insecgeo

def three2twod(shp):
    if shp is not None:
        mgeom = shp['paths']
        glen = len(mgeom) # rtepaths[0][len(rtepaths[0])-1] 
        smupltxt = ""
        if glen>0:
            smupline = []
            for il,linex in enumerate(mgeom,0):
                for xy in linex:
                    xylist = []
                    for i,x in enumerate(xy,1):
                        if i==1:
                            xylist.append(x)
                        elif i==2:
                            xylist.append(x)
                    smupline.append(xylist)
        smuplinef = [smupline]
    else:
        smuplinef = []
    return smuplinef

def rtesectmp(lyrts,rteid,bmpvalx,empvalx,offs):
    if arcpy.Exists(mptbl):    
        if int(arcpy.GetCount_management(mptbl).getOutput(0)) > 0:
            arcpy.DeleteRows_management(mptbl)
    bmpval = bmpvalx
    empval = empvalx
    rteFCSel = "RteSelected"
    rtevenTbl = "RteLinEvents"
    eveLinlyr = "lrtelyr" #os.path.join('in_memory','lrtelyr')
    arcpy.env.overwriteOutput = True
    rtegeo = None
    lyrname = lyrts.properties.name
    featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteid,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
    if (len(featlnclrte)<=0):
        if rteid == "5600":
            rteid="560"
        else:
            rteid="560"    
        featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteid,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
    if (len(featlnclrte)>0):
        rteFCSel = featlnclrte.save('in_memory','rtesel')
        ftlnclrte = featlnclrte.features
        rtegeo = ftlnclrte[0].geometry
        geomrte = deepcopy(rtegeo) # arcgis.geometry.Geometry(rtegeo,sr=sprefwebaux)
        rtepaths = rtegeo['paths']
        rtept1 = rtepaths[0][0] # geomrte.first_point
        rtept2 = rtepaths[0][len(rtepaths[0])-1] #geomrte.last_point
        bmprte = rtept1[2]
        emprte = rtept2[2]
        if bmprte==None and emprte==None:
            insecgeo = three2twod(rtegeo)
            #insecgeo = Geometry({ "paths" : insecgeo , "spatialReference" : sprefwebaux })
            insecgeo =arcgis.geometry.Geometry({ "paths" : insecgeo , "spatialReference" : sprefwebaux }) #(insecgeo,sr=sprefwebaux)
            lengeo = insecgeo.length
            insecgeo = insecgeo.project_as(sprefwgs84 ) #sprefwebaux) #insecgeo.project_as(sprefwgs84)
            print('Blank value found for  Route {} ; Rte pre-geometry {} ; projected {} ; new {}  ; length : {} ; layer {} , rte {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format
                  (rteid,rtegeo,geomrte,insecgeo,lengeo,lyrname,rteid,bmpvalx,empvalx,bmprte,emprte,offs ))
            logger.error('Blank value found for Route {} ; Rte pre-geometry {} ; projected {} ; new {}  ; length : {} ; layer {} , rte {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format
                  (rteid,rtegeo,geomrte,insecgeo,lengeo,lyrname,rteid,bmpvalx,empvalx,bmprte,emprte,offs ))
        else:
            if bmprte==None:
                bmprte = emprte - 0.01
            if emprte==None:
                emprte = bmprte + 0.01
                
            bmprte = round(bmprte,3)
            emprte = round(emprte,3)
            if (empval<bmpval):
                inpval = empval
                empval=bmpval
                bmpval = inpval
            elif (round(empval,3)==0 and bmpval<=0):
                empval=bmpval + 0.01
                    
            if (bmpval<bmprte):
                bmpval=bmprte
            if (bmpval>emprte):
                bmpval=bmprte
            if (empval>emprte):
                empval=emprte
    
            #rteFCSel = featlnclrte.save(lcfgdboutpath,'rtesel')
            arcpy.env.outputMFlag = "Disabled"
            lrte = os.path.join('in_memory','rteselyr')
            arcpy.CreateRoutes_lr(rteFCSel,RteFld.name, lrte, "TWO_FIELDS", bmpFld.name, empFld.name)
            flds = ['OBJECTID', 'SHAPE@JSON', 'ROUTE'] # selected fields in Route
            lrterows = arcpy.da.SearchCursor(lrte,flds)
            
            if (abs(empval-bmpval)<0.01):
                bmpval=max(bmpval,empval)-0.005
                empval=bmpval+0.01
            mpinscur.insertRow((rteid.upper(), bmpval,empval,offs))
            dirnlbl = 'LEFT'
            arcpy.MakeRouteEventLayer_lr(lrte,fldrte,mptbl,eveProLines, eveLinlyr,ofFld.name,"ERROR_FIELD","ANGLE_FIELD",'NORMAL','ANGLE',dirnlbl)
            # get the geoemtry from the result layer and append to the section feature class
            if arcpy.Exists(eveLinlyr):    
                cntLyr = arcpy.GetCount_management(eveLinlyr)
            if cntLyr.outputCount > 0:
                #lrsectfldnms = [ f.name for f in arcpy.ListFields(eveLinlyr)]
                insecgeo = None
                # dynamic segementaiton result layer fields used to create the closure segment  
                lrsectfldnms = ['ObjectID', 'Route', 'BMP', 'EMP', 'Shape@JSON']
                evelincur = arcpy.da.SearchCursor(eveLinlyr,lrsectfldnms)
                for srow in evelincur:
                    #insecgeo = srow.getValue("SHAPE@")
                    #print("id : {} , Rte : {} , BMP {} , EMP : {} , Geom : {} ".format(srow[0],srow[1],srow[2],srow[3],srow[4]))
                    rtenum = srow[1]
                    insecgeo = arcgis.geometry.Geometry(srow[4])
                    if insecgeo == None:
                        print('Not able to create section geometry for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrname,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                        logger.info('Not able to create section geometry for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrname,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                        insecgeo = geomrte.project_as(sprefwgs84)
                    else:
                        #print('created project section for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrname,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                        #logger.info('created project section for layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrname,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
                        insecgeo = insecgeo.project_as(sprefwgs84)
                del evelincur,lrte        
        del rteFCSel,rtevenTbl  
    else:
        rteidx = "460"  # Molokaii route 0 to 15.55 mileage
        print('Route {} not found using {} to create section geometry layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(rteid,rteidx,lyrname,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
        logger.info('Route {} not found using {} to create section geometry layer {} , on Route {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(rteid,rteidx,lyrname,rteid,bmpvalx,empvalx,bmpval,empval,offs ))
        featlnclrte = lyrts.query(where = "Route in  ({}{}{}) ".format(" '",rteidx,"' "),return_m=True,out_fields='*') #.sdf # + ,out_fields="globalid")
        ftlnclrte = featlnclrte.features
        if (len(ftlnclrte)>0):
            rtegeo = ftlnclrte[0].geometry
            geomrte = arcgis.geometry.Geometry(rtegeo)
            insecgeo = geomrte.project_as(sprefwgs84)
        else:
            insecgeo=rtegeo    
    print('Layer {} ; Route {} created section geometry {} ; original BMP : {} ; EMP : {} ; section BMP : {} ; EMP : {} ; offset {}.'.format(lyrname,rteid,insecgeo,bmpvalx,empvalx,bmpval,empval,offs ))
    return insecgeo

def mergeometry(geomfeat):
    mgeom = geomfeat.geometry
    if len(geomfeat)>0:
        rtegeo = geomfeat.geometry
        geomrte = arcgis.geometry.Geometry(rtegeo,sr=sprefwebaux)
        rtepaths = rtegeo['paths']
        rtept1 = rtepaths[0][0] # geomrte.first_point
        glen = len(rtepaths) # rtepaths[0][len(rtepaths[0])-1] 
        rtept2 = rtepaths[glen-1][len(rtepaths[glen-1])-1] #geomrte.last_point
        mgeom =[ [ x for sublist in rtepaths for x in sublist] ]
    return mgeom

def assyncadds(lyr1,fset):
    sucs1=0
    pres = None
    t1 = 0
    while(sucs1<=0 and t1<10):
        pres = lyr1.edit_features(adds=fset) #.append(prjfset) #.append(prjfset,field_mappings=fldmaprj)
        if pres['addResults'][0]['success']==True:
            sucs1=1
        else:
            t1 += 1
            sleep(7)
    return pres

def assyncaddspt(lyr1,fset):
    sucs1=0
    pres = None
    t1 = 0
    while(sucs1<=0 and t1<5):
        pres = lyr1.edit_features(adds=fset) #.append(prjfset) #.append(prjfset,field_mappings=fldmaprj)
        if pres['addResults'][0]['success']==True:
            sucs1=1
        else:
            t1 += 1
            sleep(5)
    return pres

#Get date and time
def qryhistdate(bdate,d1=0):
    dateqry = datetime.strftime((bdate-timedelta(days=d1)),"%m-%d-%Y")
    return dateqry

def setdates(sdfset,begdte,endte):
    sdfset['beginDate']= sdfsectapp['beginDate'].apply(lambda x : begdti) 
    sdfset['enDate'] = sdfsectapp['enDate'].apply(lambda x : endti) 
    sdfset['begDyWk'] = sdfsectapp['beginDate'].apply(lambda x :  datetime.strftime(x,'%A')) 
    sdfset['enDyWk'] = sdfsectapp['enDate'].apply(lambda x :  datetime.strftime(x,'%A'))
    # sdfsectapp.loc[0,'enDate'].day_name() #sdfsectapp.loc[0,'enDate'].day_name()
    return sdfset

def lanestypeside(clside,cltype,nlanes):
    if clside.upper()=="BOTH":
        lts = cltype + " closure " + clside.lower() + " lanes"
    elif clside.upper() in ["RIGHT","LEFT" ,"CENTER"]:
        if nlanes>1:
            lts = str(nlanes) + " " + clside.lower() + " lanes closed"
        else:
            lts = clside.capitalize() + " lane closed"
    elif clside.upper()=="DIRECTIONAL":
        lts = "Lanes closed in one direction"
    elif clside.upper()=="SHIFT":
        lts="Lanes shifted"
    elif clside.upper()=="FULL":
        lts = "Full lane closure" 
    return lts        
    #[ClosureSide]="Right",IIf([NumLanes]>1,[NumLanes] & " right lanes closed","Right lane closed"),[ClosureSide]="Left",IIf([NumLanes]>1,[NumLanes] & " left lanes closed","Left lane closed"),[ClosureSide]="Center",IIf([NumLanes]>1,[NumLanes] & " center lanes closed","Center lane closed"),[ClosureSide]="Full","Full lane closure",[ClosureSide]="Directional","Lanes closed in one direction",[ClosureSide]="Shift","Lanes shifted")

#OnRoad: IIf([Route]="H-1" Or [Route]="H-2" Or [Route]="H-3",[Route],IIf([Route]="H-201",[RoadName],IIf(Left([Route],2)="H-",Left([Route],3) & " off ramp",[RoadName])))
def routeinfo(rteid,rtename):
    if rteid.upper() in ["H-1", "H-2", "H-3"]:
        rtext = rteid.upper() 
    elif rteid.upper() in ["H-201"]:
        rtext = rtename 
    elif rteid[1:2] =="H-":
        rtext = "Off Ramp" 
    else:
        rtext = rtename 
    return rtext    

#DirectionWords: IIf([direct] Is Null,""," in " & [direct] & " direction")
def dirinfo(dirn):
    if len(dirn)==0:
        dirtext = ""
    else:
        dirtext = dirn + " direction " 
    return dirtext

def calc(lyr,qry):
    fld = "todayis"
    val = datemidnight(datetime.today()) 
    valx = datetime.strftime(datemidnight(datetime.today()),'%Y%m%d') 
    fld0 = "Friday0"
    expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,val) +chr(125) # 'value' : "\ �dot_achung�  
    # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
    qry0 = "format({},'yyyyMMdd') <> '{}'".format(fld,valx)
    #qry0 = "'{}' <> {}".format(val,fld)
    try:
        result = lyr.calculate(where=qry0,calc_expression={"field" : fld , "value" : val})
        print (" Update result {} for  {} ".format (result,expn))
        logger.info ("  Update result {} for  {} ".format (result,expn))
    except Exception as e:
        print (" Error message : {} \n date update calculation : {} {} failed at time {} ".format(str(e),lyr,qry0,tbeg))
        logger.error(" Error message : {} date update calculation for {} {} failed at {} ".format(str(e),lyr,qry0,tbeg))
# Check if Friday is already updated
    fri0 = fridaywk(val,0)
    fld1 = "Friday1"
    qry1 = "'{}' <> format(GETDATE({},'yyyyMMdd'))".format(valx,fld)
    #result = lyr.calculate(where=qry1,calc_expression={"field" : fld , "value" : val})
    #print (" Update result {} for  {} ".format (result,expn))
    #logger.info ("  Update result {} for  {} ".format (result,expn))
    qry1='1=1'
    lnclsectqry = lyr.query(where=qry1)
    if (qry1>0):
        fri1 = fridaywk(val,1)
        fld2 = "Friday2"
        fri2 = fridaywk(val,2)
        expn2 = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld0,fri0) +chr(125) # 'value' : "\ �dot_achung�  
        # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
        resultupd2 = wmlnclyrsects.calculate(where=qry1,calc_expression={"field" : fld0 , "value" : fri0})
        print (" Update result {} for  {} ".format (resultupd2,expn2))
        logger.info ("  Update result {} for  {} ".format (resultupd2,expn2))
    
        expn3 = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld1,fri1) +chr(125) # 'value' : "\ �dot_achung�  
        # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
        resultupd3 = wmlnclyrsects.calculate(where=qry1,calc_expression={"field" : fld1 , "value" : fri1})
        print (" Update result {} for  {} ".format (resultupd3,expn3))
        logger.info ("  Update result {} for  {} ".format (resultupd3,expn3))
    
        expn4 = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld2,fri2) +chr(125) # 'value' : "\ �dot_achung�  
        # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
        resultupd4 = wmlnclyrsects.calculate(where=qry1,calc_expression={"field" : fld2 , "value" : fri2})
        print (" Update result {} for  {} ".format (resultupd4,expn4))
        logger.info ("  Update result {} for  {} ".format (resultupd4,expn4))

def calcexpn(lyr,qry,fld,val):
    expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,val) +chr(125) # 'value' : "\ �dot_achung�  
    sucs1=0
    errcnt = 0
    resultupd = None
    lyrname = lyr.properties.name
    while(round(sucs1)==0):
        # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
        try:
            resultupd = lyr.calculate(where=qry,calc_expression={"field" : fld , "value" : val})
            print (" Update {} result {} for  {} ".format (lyrname,resultupd,expn))
            logger.info ("  Update {} result {} for  {} ".format (lyrname,resultupd,expn))
            if resultupd['success']==True:
                sucs1=1
            else:
                errcnt+=1
                terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
                print("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, resultupd,lyrname,fld,val))
                logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, resultupd,lyrname,fld,val))
                if errcnt<=10:
                    sleep(10)
                else:
                    sucs1=-1
        except Exception as e:
            print (" Attempt Error message : {} date update calculation : {} using query {} resulting {} failed at {}".format(str(e),lyrname,qry,resultupd,tbeg))
            logger.error(" Attempt Error message : {} date update calculation for {} using query {} resulting {} failed at {} ".format(str(e),lyrname,qry,resultupd,tbeg))
    return resultupd

def calcfridayx(lyr,oidfld,maxoid,fld,x):
    # x = 0 for last week friday, 1 for this week friday, 2 for next week friday
    val = datemidnight(datetime.today()) 
    valx = datetime.strftime(datemidnight(datetime.today()),'%Y%m%d') 
    lyrname = lyr.properties.name
    oidval1 = 0
    while maxoid >= oidval1  :
        oidval2 = oidval1+10000
        qry = "{} between '{}' and '{}'".format(oidfld,oidval1,oidval2)
        sucs1 = 0
        while(round(sucs1)==0):
            expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,val) +chr(125) # 'value' : "\ �dot_achung�  
            # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
            qry0 = "format({},'yyyyMMdd') <> '{}'".format(fld,valx)
            #qry0 = "'{}' <> {}".format(val,fld)
        # Check if Friday is already updated
            fri = fridaywk(val,x)
            expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,fri) +chr(125) # 'value' : "\ �dot_achung�  
            pres = calcexpn(lyr,qry,fld,fri)
            if pres['success']==True:
                sucs1=1
                print (" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn,pres,lyrname))
                logger.info(" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn,pres,lyrname))
            else:
                errcnt+=1
                terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
                logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, pres,lyrname,fld,fri))
                #if errcnt<=10:
                sleep(10)
        oidval1 = oidval2
    return pres

def calcfridays(lyr,oidfld):
    fld = "todayis"
    val = datemidnight(datetime.today()) 
    valx = datetime.strftime(datemidnight(datetime.today()),'%Y%m%d') 
    lyrname = lyr.properties.name
    oidval1 = 0
    outstat = [{"statisticType": "max","onStatisticField": oidfld,"outStatisticFieldName": "maxoid"}]
    print (" layer  {} query {} ".format (lyrname,outstat))
    maxres = lyr.query(out_statistics=outstat).sdf
    maxoid =  maxres["maxoid"][0]
    print (" Update {} query {} result  {} ".format (lyrname,outstat,maxoid))
    logger.info (" Update {} query {} result  {} ".format (lyrname,outstat,maxoid))
    while maxoid >= oidval1  :
        oidval2 = oidval1+10000
        qry = "{} between '{}' and '{}'".format(oidfld,oidval1,oidval2)
        sucs1 = 0
        while(round(sucs1)==0):
            fld0 = "Friday0"
            expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,val) +chr(125) # 'value' : "\ �dot_achung�  
            # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
            qry0 = "format({},'yyyyMMdd') <> '{}'".format(fld,valx)
            #qry0 = "'{}' <> {}".format(val,fld)
        # Check if Friday is already updated
            fri0 = fridaywk(val,0)
            expn0 = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld0,fri0) +chr(125) # 'value' : "\ �dot_achung�  
            pres0 = calcexpn(lyr,qry,fld0,fri0)
            if pres0['success']==True:
                sucs1=1
                print (" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn0,pres0,lyrname))
                logger.info(" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn0,pres0,lyrname))
            else:
                errcnt+=1
                terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
                logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, pres0,lyrname,fld0,fri0))
                #if errcnt<=10:
                sleep(10)

        sucs1 = 0
        while(round(sucs1)==0):
            fld1 = "Friday1"
            fri1 = fridaywk(val,1)
            expn1 = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld1,fri1) +chr(125) # 'value' : "\ �dot_achung�  
            pres1 = calcexpn(lyr,qry,fld1,fri1)
            if pres1['success']==True:
                sucs1=1
                print (" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn1,pres1,lyrname))
                logger.info(" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn1,pres1,lyrname))
            else:
                errcnt+=1
                terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
                logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, pres1,lyrname,fld1,fri1))
                #if errcnt<=10:
                sleep(10)
 
        sucs1 = 0
        while(round(sucs1)==0):
            fld2 = "Friday2"
            fri2 = fridaywk(val,2)
            expn2 = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld2,fri2) +chr(125) # 'value' : "\ �dot_achung�  
            pres2 = calcexpn(lyr,qry,fld2,fri2)
            if pres2['success']==True:
                sucs1=1
                print (" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn2,pres2,lyrname))
                logger.info(" update {} current date {} ; response : {} ;  Layer {} ".format(qry,expn2,pres2,lyrname))
            else:
                errcnt+=1
                terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
                logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, pres2,lyrname,fld2,fri2))
                #if errcnt<=10:
                sleep(10)
        oidval1 = oidval2
    return (pres0,pres1,pres2)

def calctoday(lyr,qry,fld,valdte):
    #fld = "todayis"
    #val =  datemidnight(datetime.today(),0) # "CURRENT_DATE()" #
    expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,valdte) +chr(125) # 'value' : "\ “dot_achung”  
    # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
    sucs1=0
    errcnt = 0
    pres = None
    lyrname = lyr.properties.name
    while(round(sucs1)==0):
        pres = lyr.calculate(where=qry,calc_expression={"field" : fld , "value" : valdte}) #.append(prjfset) #.append(prjfset,field_mappings=fldmaprj)
        if pres['success']==True:
            sucs1=1
        else:
            errcnt+=1
            terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
            logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, pres,lyrname,fld,valdte))
            #if errcnt<=10:
            sleep(5)
    
    print (" Update {} result {} for  {} ".format (lyrname,pres,expn))
    logger.info ("  Update {} result {} for  {} ".format (lyrname,pres,expn))
    return pres

""" # FullSentence: [LanesTypeSide] & " on " & [OnRoad] & [DirectionWords] & IIf([BeginDateName]=[EndDateName]," on " 
& [BeginDay] & ", " & [BeginDateName]," from " & [BeginDay] & ", " & [BeginDateName] & " to " & [EndDay] & ", " 
& [EndDateName]) & ", " & [BeginTime] & " to " & [EndTime] & " " & [Special Remarks]
"""
def fulltext (lts,rtext,dirtext,begdymon,endymon,begdynm,endynm,begtm,endtm,begint,endint,rmarks):
    #fultext = lts + " on " + rtext + dirtext 
    if (begint==endint):
        begendint = "In the vicinity of {}".format(begint)
    else:
        begendint = "Between intersections of {} and {}".format(begint,endint)
            
    if begdynm == endynm:
        fultext = "{} on {}  {} on {}, {}, {} to {} ,  {} . {} .".format(lts, rtext, dirtext, begdynm, begdymon,begendint,rmarks)
    else:    
        fultext = "{} on {}  {} from {}, {}, to {} , {} , {} to {} , {} , Additional Remarks : {}.".format(lts, rtext, dirtext, begdynm, begdymon,endynm, endymon,begtm, endtm,begendint,rmarks) 
    return fultext

def calctodayx(lyr,qry,fld,valdte):
    #fld = "todayis"
    #val =  datemidnight(datetime.today(),0) # "CURRENT_DATE()" #
    oidfld = 'objectid'
    oidval = 20000
    qryStr0 = "{} <= '{}'".format(oidfld,oidval)
    expn = chr(123) + "\"field\" : \"{}\" , \"value\" : \"{}\"".format(fld,valdte) +chr(125) # 'value' : "\ “dot_achung”  
    # (where=qryStr0,calc_expression={"field" : "l2email" , "value" : "Mike.Medeiros@hawaii.gov"}) 
    sucs1=0
    errcnt = 0
    pres = None
    oidval1 = 0
    lyrname = lyr.properties.name
    outstat = [{"statisticType": "max","onStatisticField": oidfld,"outStatisticFieldName": "maxoid"}]
    print (" layer  {} query {} ".format (lyrname,outstat))
    maxres = lyr.query(out_statistics=outstat).sdf
    maxoid =  maxres["maxoid"][0]
    tqry = datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
    print (" Update {} query {} total records {} begins at {}".format (lyrname,outstat,maxoid,tqry))
    logger.info (" Update {} query {} ; total records {} begins at {}".format (lyrname,outstat,maxoid,tqry))
    while maxoid >= oidval1  :
        oidval2 = oidval1+10000
        qry = "{} between '{}' and '{}'".format(oidfld,oidval1,oidval2)
        sucs1 = 0
        while(round(sucs1)==0):
            pres = lyr.calculate(where=qry,calc_expression={"field" : fld , "value" : valdte}) #.append(prjfset) #.append(prjfset,field_mappings=fldmaprj)
            if pres['success']==True:
                sucs1=1
                print (" update {} current date {} ; response : {} ;  Layer {} ".format(qry,valdte,pres,lyrname))
                logger.info(" update {} current date {} ; response : {} ;  Layer {} ".format(qry,valdte,pres,lyrname))
            else:
                errcnt+=1
                terr = datetime.datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
                logger.error("Attempt {} at {} ; Result : {} ; Layer {} ; fld {} ; value {} ".format(errcnt,terr, pres,lyrname,fld,valdte))
                #if errcnt<=10:
                sleep(10)
    
        oidval1 = oidval2
    tqry = datetime.today().strftime("%A, %B %d, %Y at %H:%M:%S %p")
    print (" Update {} result {} for  {} records completed at {} ".format (lyrname,pres,maxoid,tqry))
    logger.info ("  Update {} result {} for  {} records completed at {} ".format (lyrname,pres,maxoid,tqry))
    return pres

def logResult(fourby, res):
    logStr = fourby + ": " + str(res) + "\n"
    logFile = open(logpath, 'a')
    logFile.write(logStr)
    logFile.close()

def replace(client,fourby, df):
    data = df.to_dict(orient='records', into=NativeDict)
    # pprint(data)

    # set up client for api calls
    #client = Socrata(url, app_token, username=user, password=password)
    # upsert new row using client
    try:
        res = client.replace(fourby, data)
    except Exception as e:
        print('whoops')
        res = e

    logResult(fourby, res)
    print(res)
    client.close()

    return res

class NativeDict(dict):
    """
        Helper class to ensure that only native types are in the dicts produced by
        :func:`to_dict() <pandas.DataFrame.to_dict>`
    """
    def __init__(self, *args, **kwargs):
        super().__init__(((k, self.convert_if_needed(v)) for row in args for k, v in row), **kwargs)

    @staticmethod
    def convert_if_needed(value):
        """
            Converts `value` to native python type.
        """
        if isnull(value):
            return None
        if isinstance(value, pd.Timestamp):
            return value.isoformat()
        if hasattr(value, 'dtype'):
            mapper = {'i': int, 'u': int, 'f': float}
            _type = mapper.get(value.dtype.kind, lambda x: x)
            return _type(value)
        if value == 'NaT':
            return None
        if isinstance(value, numpy.datetime64):
            return value
        return value

#Fill DirpRemarks field with long remarks data if it is blank
def remarkstext(remarks,dirptext):
    if dirptext != None:
        if len(dirptext)>100:
            dirptext = remarks[0:99]
    return dirptext

def socratamultilineshp(shp):
    if shp is not None:
        mgeom = shp['paths']
        glen = len(mgeom) # rtepaths[0][len(rtepaths[0])-1] 
        smupltxt = ""
        if glen>0:
            smupline = []
            for il,linex in enumerate(mgeom,0):
                smupline.append([])
                for xy in linex:
                    xylist = ""
                    for i,x in enumerate(xy,1):
                        if i==1:
                            xylist = str(x)
                        elif i==2:
                            xylist = xylist + " " + str(x)
                    smupline[il].append(xylist)
    else:
        smupline = ""
    smupltxt = "MultiLineString {}".format(smupline)
    smupltxt = smupltxt.replace("'","").replace("[","(").replace("]",")")            
    return smupltxt

def soclinegometry(shp):
    slinetxt = ""
    if shp is not None:
        mgeom = shp['paths']
        glen = len(mgeom) # rtepaths[0][len(rtepaths[0])-1] 
        if glen>0:
            socline = []
            for il,linex in enumerate(mgeom,0):
                for xy in linex:
                    xylist = ""
                    for i,x in enumerate(xy,1):
                        if i==1:
                            xylist = str(x)
                        elif i==2:
                            xylist = xylist + " " + str(x)
                    socline.append(xylist)
    else:
        socline = ""
    slinetxt = "LineString {}".format(socline)
    slinetxt = slinetxt.replace("'","").replace("[","(").replace("]",")")            
    return slinetxt

def recs2htmlbody(featsdf,htmltd,urlinkx):
    # merge relationship records from the child table to the current header record
    htmlby = "" #htmltxtd.format(q1="\"",urlink=urlinkx,q2="\"",island=sdfrec.Island,route=sdfrec.Route,begindate=sdfrec.beginDate,endate=sdfrec.enDate,intersfrom=sdfrec.IntersFrom,intersto=sdfrec.IntersTo) + "\n"
    for ir,sdfrec in enumerate(featsdf.itertuples()):   # two points are given                                                                                                                                                                                                                                                                                                                                                                                       
    # add two sets of columns from the related data to the header data frame                                                                                                                                                                                                                                                                                                                                                                                             
        htmlby = htmlby + htmltd.format(q1="\"",urldet=urlinkx,fldid="OBJECTID",fldval=sdfrec.OBJECTID,q2="\"",island=sdfrec.Island,route=sdfrec.Route,roadname=sdfrec.RoadName,intersfrom=sdfrec.IntersFrom,intersto=sdfrec.IntersTo,begindate=sdfrec.beginDate,endate=sdfrec.enDate) + "\n"
    
    return htmlby

def dateonly(bdate,h1=0):
    datemid = datetime.strptime(datetime.strftime(bdate,"%Y-%m-%d"),"%Y-%m-%d") + timedelta(hours=h1)
    return datemid

def submit_request(request):
    """ Returns the response from an HTTP request in json format."""
    with contextlib.closing(urllib.request.urlopen(request)) as response:
        content = response.read()
        content_decoded = content.decode("utf-8")
        job_info = json.loads(content_decoded)
        return job_info

def get_token(portal_url, username, password):
    """ Returns an authentication token for use in ArcGIS Online."""

    # Set the username and password parameters before
    #  getting the token. 
    #
    params = {"username": username,
              "password": password,
              "referer": "http://www.arcgis.com",
              "f": "json"}

    token_url = "{}/generateToken".format(portal_url)
    data = urllib.parse.urlencode(params)
    data_encoded = data.encode("utf-8")
    request = urllib.request.Request(token_url, data=data_encoded)
    token_response = submit_request(request)
    if "token" in token_response:
        print("Getting token...")
        token = token_response.get("token")
        return token
    else:
        # Request for token must be made through HTTPS.
        #
        if "error" in token_response:
            error_mess = token_response.get("error", {}).get("message")
            if "This request needs to be made over https." in error_mess:
                token_url = token_url.replace("http://", "https://")
                token = get_token(token_url, username, password)
                return token
            else:
                raise Exception("Portal error: {} ".format(error_mess))

def get_analysis_url(portal_url, token):
    """ Returns Analysis URL from AGOL for running analysis services."""

    print("Getting Analysis URL...")
    portals_self_url = "{}/portals/self?f=json&token={}".format(portal_url, token)
    request = urllib.request.Request(portals_self_url)
    portal_response = submit_request(request)

    # Parse the dictionary from the json data response to get Analysis URL.
    #
    if "helperServices" in portal_response:
        helper_services = portal_response.get("helperServices")
        if "analysis" in helper_services:
            analysis_service = helper_services.get("analysis")
            if "url" in analysis_service:
                analysis_url = analysis_service.get("url")
                return analysis_url
    else:
        raise Exception("Unable to obtain Analysis URL.")

def analysis_job(analysis_url, task, token, params):
    """ Submits an Analysis job and returns the job URL for monitoring the job
        status in addition to the json response data for the submitted job."""
    
    # Unpack the Analysis job parameters as a dictionary and add token and
    # formatting parameters to the dictionary. The dictionary is used in the
    # HTTP POST request. Headers are also added as a dictionary to be included
    # with the POST.
    #
    print("Submitting analysis job...")
    
    params["f"] = "json"
    params["token"] = token
    headers = {"Referer":"http://www.arcgis.com"}
    task_url = "{}/{}".format(analysis_url, task)
    submit_url = "{}/submitJob?".format(task_url)
    data = urllib.parse.urlencode(params)
    data_encoded = data.encode("utf-8")
    request = urllib.request.Request(submit_url, data=data_encoded, headers=headers)
    analysis_response = submit_request(request)
    if analysis_response:
        # Print the response from submitting the Analysis job.
        #
        print(analysis_response)
        return task_url, analysis_response
    else:
        raise Exception("Unable to submit analysis job.")

def analysis_job_status(task_url, job_info, token):
    """ Tracks the status of the submitted Analysis job."""

    if "jobId" in job_info:
        # Get the id of the Analysis job to track the status.
        #
        job_id = job_info.get("jobId")
        job_url = "{}/jobs/{}?f=json&token={}".format(task_url, job_id, token)
        request = urllib.request.Request(job_url)
        job_response = submit_request(request)

        # Query and report the Analysis job status.
        #
        if "jobStatus" in job_response:
            while not job_response.get("jobStatus") == "esriJobSucceeded":
                time.sleep(5)
                request = urllib.request.Request(job_url)
                job_response = submit_request(request)
                print(job_response)

                if job_response.get("jobStatus") == "esriJobFailed":
                    raise Exception("Job failed.")
                elif job_response.get("jobStatus") == "esriJobCancelled":
                    raise Exception("Job cancelled.")
                elif job_response.get("jobStatus") == "esriJobTimedOut":
                    raise Exception("Job timed out.")
                
            if "results" in job_response:
                return job_response
        else:
            raise Exception("No job results.")
    else:
        raise Exception("No job url.")
                        
def analysis_job_results(task_url, job_info, token):
    """ Use the job result json to get information about the feature service
        created from the Analysis job."""

    # Get the paramUrl to get information about the Analysis job results.
    #
    if "jobId" in job_info:
        job_id = job_info.get("jobId")
        if "results" in job_info:
            results = job_info.get("results")
            result_values = {}
            for key in list(results.keys()):
                param_value = results[key]
                if "paramUrl" in param_value:
                    param_url = param_value.get("paramUrl")
                    result_url = "{}/jobs/{}/{}?token={}&f=json".format(task_url, 
                                                                        job_id, 
                                                                        param_url, 
                                                                        token)
                    request = urllib.request.Request(result_url)
                    param_result = submit_request(request)
                    job_value = param_result.get("value")
                    result_values[key] = job_value
            return result_values
        else:
            raise Exception("Unable to get analysis job results.")
    else:
        raise Exception("Unable to get analysis job results.")
        
#Fill DirpRemarks field with long remarks data if it is blank
def remarkstextold(remarks,dirptext):
    if len(dirptext)==0:
        dirptext = remarks[0:99]
    return dirptext

def remarkstextx(remarks,dirptext):
    try:
        if isinstance(dirptext,str):
            if len(dirptext)>100:
                if isinstance(remarks,str):
                    dirptext = remarks[0:99]
                else:
                    dirptext = "No remarks"
        else:
                if isinstance(remarks,str):
                    dirptext = remarks[0:99]
                else:
                    dirptext = "No remarks"
            
    except Exception as e:
        print (" Error message : {} remarks report text {} ".format(str(e),dirptext))
        logger.error(" Error message : {} remarks report text {} ".format(str(e),dirptext))
        if isinstance(remarks,str):
            dirptext = remarks[0:99]
        else:
            dirptext = "No remarks"
    return dirptext

def routenames(rdname,rte):
    if rdname == None:
        rdname = rte
    elif len(rdname)==0:
        rdname = rte
    return rdname

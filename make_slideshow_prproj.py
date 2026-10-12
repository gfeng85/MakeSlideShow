#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
make_slideshow_prproj.py —— 照片幻灯片 Premiere 工程生成器
============================================================
把 PIC 目录（或任意照片目录）下的照片批量生成一个 Adobe Premiere Pro
工程文件(.prproj)，自动完成：

  1. 照片按文件名自然排序导入工程素材库；
  2. 每张照片在时间线上播放 3~5 秒（可参数调整，随机时长）；
  3. 每张照片两层：
       - V1 背景层：同照片按“宽度铺满”缩放 + 高斯模糊（默认模糊度 300）；
       - V2 前景层：横图按“满屏铺满”、竖图按“高度铺满”缩放，
         并叠加随机的轻微“缩放推近 / 缩放拉远 / 左右上下平移”运动
         （Ken Burns 效果，幅度很小，最大缩放默认不超过 110%）；
  4. 相邻照片之间使用随机的视频过渡效果（交叉溶解 / 中心拆分 /
     VR 光圈擦除，与 example\\未命名.prproj 示例一致）。


用法示例：
  python make_slideshow_prproj.py
  python make_slideshow_prproj.py --pic-dir D:\\photos --out D:\\out.prproj \
         --min-dur 3 --max-dur 5 --width 3840 --height 2160 --seed 42
"""
import argparse
import base64
import gzip
import math
import os
import random
import re
import shutil
import struct
import sys
import uuid
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape

from prproj_templates import (
    T_VIEWSTATE, T_SETTINGS, T_AUDIOTRACKS, T_AUDIOCOMPS,
    T_AUDIOFADERS, T_AUDIOPARAMS,
)

SEQ_TB = 254016000000          # Premiere 主时间基准 (ticks/s)
SEQ_FRAME = SEQ_TB // 30       # 30fps 序列每帧 ticks
SRC_FRAME = SEQ_TB // 25       # 静帧源帧率(25fps)每帧 ticks
MEDIA_DURATION = 10973491200000000
SRC_ORIGINAL_DURATION = 10973491200000000

MOTION_HASH = "3805854c-243a-c4be-bd40-a8a40000000e"
IRIS_HASH = "5d74e13e-61cb-28d5-98f8-ffc20000004c"
IRIS_BODY = "eyJ2ZXJzaW9uIjoxLCJ2cmF0dHJpYnV0ZXMiOnsiaGZvdiI6MzYwLCJsYXlvdXQiOjAsInZmb3YiOjE4MH19AA=="


# ---------------------------------------------------------------------------
# 图片尺寸探测（纯标准库）
# ---------------------------------------------------------------------------
def img_size(path):
    try:
        with open(path, "rb") as f:
            head = f.read(32)
        if head[:2] == b"\xff\xd8":                      # JPEG
            with open(path, "rb") as f:
                b = f.read(262144)
            i = 2
            n = len(b)
            while i + 9 < n:
                if b[i] != 0xFF:
                    i += 1
                    continue
                m = b[i + 1]
                if m in (0xC0, 0xC1, 0xC2, 0xC3, 0xC5, 0xC6, 0xC7,
                         0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
                    h = struct.unpack(">H", b[i + 5:i + 7])[0]
                    w = struct.unpack(">H", b[i + 7:i + 9])[0]
                    return (w, h) if w and h else None
                if m in (0xD8, 0xD9) or 0xD0 <= m <= 0xD7:
                    i += 1
                    continue
                ln = struct.unpack(">H", b[i + 2:i + 4])[0]
                if ln < 2:
                    return None
                i += 2 + ln
            return None
        if head[:8] == b"\x89PNG\r\n\x1a\n":             # PNG
            w = struct.unpack(">I", head[16:20])[0]
            h = struct.unpack(">I", head[20:24])[0]
            return (w, h) if w and h else None
        if head[:6] in (b"GIF87a", b"GIF89a"):           # GIF
            w = struct.unpack("<H", head[6:8])[0]
            h = struct.unpack("<H", head[8:10])[0]
            return (w, h) if w and h else None
        if head[:2] == b"BM":                            # BMP
            w = struct.unpack("<i", head[18:22])[0]
            h = abs(struct.unpack("<i", head[22:26])[0])
            return (w, h) if w and h else None
    except Exception:
        pass
    return None


# ---------------------------------------------------------------------------
# 分配器与数值格式化
# ---------------------------------------------------------------------------
class Alloc:
    def __init__(self, start=1000):
        self._n = start - 1

    def oid(self):
        self._n += 1
        return self._n

    @staticmethod
    def uid():
        return str(uuid.uuid4())


def fmt_num(v):
    """示例风格数值：整数带小数点(96.)，小数保留6位后修剪。"""
    s = f"{v:.6f}".rstrip("0").rstrip(".")
    if "." not in s:
        s += "."
    return s


def fmt_kf(v):
    return f"{v:.12g}"


def guid16le_b64(guid):
    return base64.b64encode(guid.encode("utf-16-le")).decode("ascii")


def bin_hash(size):
    return f"{uuid.uuid4().hex[:4]}{size:08x}"


def natural_key(s):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", s)]


# ---------------------------------------------------------------------------
# 静态参数模板
# ---------------------------------------------------------------------------
def param_video(alloc, name, pid, ctype, sval, low, high, upper_ui=None,
                cur=None, dclass="fe47129e-6c94-4fc0-95d5-c056a517aaf3",
                version="9", discontinuous=False):
    extra = "\n\t<DiscontinuousInterpolate>true</DiscontinuousInterpolate>" if discontinuous else ""
    cur_x = f"\n\t<CurrentValue>{cur}</CurrentValue>" if cur is not None else ""
    uu_x = f"\n\t<UpperUIBound>{upper_ui}</UpperUIBound>" if upper_ui is not None else ""
    oid = alloc.oid()
    return (
        f'<VideoComponentParam ObjectID="{oid}" ClassID="{dclass}" Version="{version}">\n'
        f'\t<Name>{escape(name)}</Name>\n'
        f'\t<IsTimeVarying>false</IsTimeVarying>\n'
        f'{extra}'
        f'\t<ParameterControlType>{ctype}</ParameterControlType>\n'
        f'\t<StartKeyframe>-91445760000000000,{sval}</StartKeyframe>\n'
        f'{cur_x}'
        f'\t<LowerBound>{low}</LowerBound>\n'
        f'\t<UpperBound>{high}</UpperBound>\n'
        f'\t<ParameterID>{pid}</ParameterID>\n'
        f'{uu_x}'
        f'</VideoComponentParam>'
    )


def param_point(alloc, name, pid, x="0.5", y="0.5"):
    oid = alloc.oid()
    return (
        f'<PointComponentParam ObjectID="{oid}" ClassID="ca81d347-309b-44d2-acc7-1c572efb973c" Version="3">\n'
        f'\t<Name>{escape(name)}</Name>\n'
        f'\t<IsTimeVarying>false</IsTimeVarying>\n'
        f'\t<ParameterControlType>6</ParameterControlType>\n'
        f'\t<StartKeyframe>-91445760000000000,{x}:{y},0,0,0,0,0,0,5,4,0,0,0,0</StartKeyframe>\n'
        f'\t<ParameterID>{pid}</ParameterID>\n'
        f'</PointComponentParam>'
    )


def param_scale_keyframed(alloc, kf0, kf1, v0, v1, slope, cur):
    keyframes = (f'{kf0},{fmt_kf(v0)},0,0,0,0.16666666666666666,{fmt_kf(slope)},0.16666666666666666;'
                 f'{kf1},{fmt_kf(v1)},0,0,{fmt_kf(slope)},0.16666666666666666,0,0.16666666666666666;')
    oid = alloc.oid()
    return (
        f'<VideoComponentParam ObjectID="{oid}" ClassID="fe47129e-6c94-4fc0-95d5-c056a517aaf3" Version="9">\n'
        f'\t<Node Version="1">\n'
        f'\t\t<Properties Version="1">\n'
        f'\t\t\t<ECP.Slider.Expanded>true</ECP.Slider.Expanded>\n'
        f'\t\t</Properties>\n'
        f'\t</Node>\n'
        f'\t<Name>缩放</Name>\n'
        f'\t<ParameterControlType>2</ParameterControlType>\n'
        f'\t<StartKeyframe>-91445760000000000,{fmt_kf(v0)},0,0,0,0,0,0</StartKeyframe>\n'
        f'\t<Keyframes>{keyframes}</Keyframes>\n'
        f'\t<CurrentValue>{fmt_kf(cur)}</CurrentValue>\n'
        f'\t<LowerBound>0</LowerBound>\n'
        f'\t<UpperBound>10000</UpperBound>\n'
        f'\t<ParameterID>2</ParameterID>\n'
        f'\t<UpperUIBound>200</UpperUIBound>\n'
        f'</VideoComponentParam>'
    )


def param_pos_keyframed(alloc, kf0, kf1, px0, py0, px1, py1, slope):
    keyframes = (f'{kf0},{fmt_kf(px0)}:{fmt_kf(py0)},0,0,0,0.16666666666666666,{fmt_kf(slope)},0.16666666666666666,5,4,0,0,0,0;'
                 f'{kf1},{fmt_kf(px1)}:{fmt_kf(py1)},0,0,{fmt_kf(slope)},0.16666666666666666,0,0.16666666666666666,5,4,0,0,0,0;')
    oid = alloc.oid()
    return (
        f'<PointComponentParam ObjectID="{oid}" ClassID="ca81d347-309b-44d2-acc7-1c572efb973c" Version="3">\n'
        f'\t<Node Version="1">\n'
        f'\t\t<Properties Version="1">\n'
        f'\t\t\t<ECP.Slider.Expanded>true</ECP.Slider.Expanded>\n'
        f'\t\t</Properties>\n'
        f'\t</Node>\n'
        f'\t<Name>位置</Name>\n'
        f'\t<ParameterControlType>6</ParameterControlType>\n'
        f'\t<StartKeyframe>-91445760000000000,{fmt_kf(px0)}:{fmt_kf(py0)},0,0,0,0,0,0,5,4,0,0,0,0</StartKeyframe>\n'
        f'\t<Keyframes>{keyframes}</Keyframes>\n'
        f'\t<ParameterID>1</ParameterID>\n'
        f'</PointComponentParam>'
    )


# ---------------------------------------------------------------------------
# 滤镜组件
# ---------------------------------------------------------------------------
def filter_component(alloc, comp_id, param_xmls, fid, display, intrinsic,
                     match, private=None):
    params = "\n".join(
        f'\t\t\t<Param Index="{i}" ObjectRef="{pid_of(p)}"/>'
        for i, p in enumerate(param_xmls)
    )
    if private is None:
        pd = ""
    else:
        body, bhash = private
        if body is None:
            pd = (f'\t<PremiereFilterPrivateData Encoding="base64" '
                  f'BinaryHash="{bhash}"/>\n')
        else:
            pd = (f'\t<PremiereFilterPrivateData Encoding="base64" '
                  f'BinaryHash="{bhash}">\n'
                  f'\t\t{body}\n'
                  f'\t</PremiereFilterPrivateData>\n')
    return (
        f'<VideoFilterComponent ObjectID="{comp_id}" ClassID="d10da199-beea-4dd1-b941-ed3a78766d50" Version="8">\n'
        f'\t<Component Version="6">\n'
        f'\t\t<Params Version="1">\n'
        f'{params}\n'
        f'\t\t</Params>\n'
        f'\t\t<ID>{fid}</ID>\n'
        f'\t\t<DisplayName>{escape(display)}</DisplayName>\n'
        f'\t\t<Bypass>false</Bypass>\n'
        f'\t\t<Intrinsic>{intrinsic}</Intrinsic>\n'
        f'\t\t<ArchivedType>0</ArchivedType>\n'
        f'\t</Component>\n'
        f'{pd}'
        f'\t<MatchName>{match}</MatchName>\n'
        f'\t<VideoFilterType>2</VideoFilterType>\n'
        f'</VideoFilterComponent>'
    )


def pid_of(param_xml):
    m = re.search(r'ObjectID="(\d+)"', param_xml)
    return int(m.group(1))


# ---------------------------------------------------------------------------
# 缺失的项目设置对象（12-39，来自示例，与照片无关的固定默认值）
# ---------------------------------------------------------------------------
_VS = ('\t<VideoSettings ObjectID="{i}" ClassID="58474264-30c4-43a2-bba5-dc0812df8a3a" Version="9">\n'
      '\t\t<FrameRate>8475667200</FrameRate>\n'
      '\t\t<FrameSize>0,0,720,480</FrameSize>\n'
      '\t\t<PixelAspectRatio>10,11</PixelAspectRatio>\n'
      '\t\t<MaximumBitDepth>false</MaximumBitDepth>\n'
      '\t</VideoSettings>')
_AS = ('\t<AudioSettings ObjectID="{i}" ClassID="6baf5521-b132-4634-840e-13cec5bc86a4" Version="7">\n'
      '\t\t<FrameRate>5292000</FrameRate>\n'
      '\t\t<ChannelType>1</ChannelType>\n'
      '\t</AudioSettings>')
_VCS = ('\t<VideoCompileSettings ObjectID="{i}" ClassID="db372db5-7de2-4d3c-98ae-f42659d77b22" Version="9">\n'
       '\t\t<VideoSettings ObjectRef="{ref}"/>\n'
       '\t\t<VideoCompilerClassIDFourCC>1061109567</VideoCompilerClassIDFourCC>\n'
       '\t\t<VideoFileTypeFourCC>1096173910</VideoFileTypeFourCC>\n'
       '\t\t<Compressor>1685288558</Compressor>\n'
       '\t\t<Depth>24</Depth>\n'
       '\t\t<Aspect43>false</Aspect43>\n'
       '\t\t<Quality>100</Quality>\n'
       '\t\t<UseDataRate>false</UseDataRate>\n'
       '\t\t<DataRate>3500</DataRate>\n'
       '\t\t<ForceRecompress>true</ForceRecompress>\n'
       '\t\t<ForceRecompressValue>2</ForceRecompressValue>\n'
       '\t\t<Deinterlace>false</Deinterlace>\n'
       '\t\t<IgnoreVideoFilters>false</IgnoreVideoFilters>\n'
       '\t\t<OptimizeStills>false</OptimizeStills>\n'
       '\t\t<FramesAtMarkers>false</FramesAtMarkers>\n'
       '\t\t<RealTimePreview>true</RealTimePreview>\n'
       '\t\t<VideoFieldType>0</VideoFieldType>\n'
       '\t\t<DoKeyframeEveryNFrames>false</DoKeyframeEveryNFrames>\n'
       '\t\t<DoKeyframeEveryNFramesValue>0</DoKeyframeEveryNFramesValue>\n'
       '\t\t<AddKeyframesAtMarkers>false</AddKeyframesAtMarkers>\n'
       '\t\t<AddKeyframesAtEdits>false</AddKeyframesAtEdits>\n'
       '\t\t<RelativeFrameSize>1</RelativeFrameSize>\n'
       '\t\t<RenderDepth>0</RenderDepth>\n'
       '\t</VideoCompileSettings>')
_ACS = ('\t<AudioCompileSettings ObjectID="{i}" ClassID="34b10007-ab6d-49a7-bac5-7b60d919e387" Version="6">\n'
       '\t\t<AudioSettings ObjectRef="{ref}"/>\n'
       '\t\t<Compressor>1380013856</Compressor>\n'
       '\t\t<Interleave>1</Interleave>\n'
       '\t\t<SampleType>3</SampleType>\n'
       '\t</AudioCompileSettings>')
_CAPTURE = ('\t<CaptureSettings ObjectID="16" ClassID="328c2aa2-47f9-4211-805b-b6a6dbd4ca29" Version="10">\n'
            '\t\t<RecordModuleDisplayName>DV</RecordModuleDisplayName>\n'
            '\t\t<SupportedFileExtension>avi</SupportedFileExtension>\n'
            '\t\t<RecorderID>0ae2b9b7-6efc-424f-aadf-1a2dedd5e8ff</RecorderID>\n'
            '\t\t<VideoFrameRate>8475667200</VideoFrameRate>\n'
            '\t\t<VideoFrameSize>0,0,720,480</VideoFrameSize>\n'
            '\t\t<VideoCompressorFourCC>0</VideoCompressorFourCC>\n'
            '\t\t<AudioCompressorFourCC>1380013856</AudioCompressorFourCC>\n'
            '\t\t<AudioCompressorDisplayName>未压缩</AudioCompressorDisplayName>\n'
            '\t\t<AudioFrameRate>7938000</AudioFrameRate>\n'
            '\t\t<AudioSampleType>3</AudioSampleType>\n'
            '\t\t<AudioChannelType>1</AudioChannelType>\n'
            '\t\t<AbortCaptureOnDroppedFrames>false</AbortCaptureOnDroppedFrames>\n'
            '\t</CaptureSettings>')
_DSEQ = ('\t<DefaultSequenceSettings ObjectID="17" ClassID="567bdf53-d6d9-4d61-b2f1-f4834bebea9b" Version="2">\n'
         '\t\t<TotalVideoTracks>1</TotalVideoTracks>\n'
         '\t\t<DefaultAudioStandardMonoTracks>0</DefaultAudioStandardMonoTracks>\n'
         '\t\t<DefaultAudioStandardStereoTracks>1</DefaultAudioStandardStereoTracks>\n'
         '\t\t<DefaultAudioStandard51Tracks>0</DefaultAudioStandard51Tracks>\n'
         '\t\t<DefaultAudioSubmixMonoTracks>0</DefaultAudioSubmixMonoTracks>\n'
         '\t\t<DefaultAudioSubmixStereoTracks>0</DefaultAudioSubmixStereoTracks>\n'
         '\t\t<DefaultAudioSubmix51Tracks>0</DefaultAudioSubmix51Tracks>\n'
         '\t</DefaultSequenceSettings>')


def x_misc_settings():
    """返回 (T_MISCSET1, T_MISCSET2) —— 示例中 ObjectID 12-27 与 28-39 的固定对象。"""
    s1 = [_VS.format(i=12), _AS.format(i=13)]
    s1.append(_VCS.format(i=14, ref=28))
    s1.append(_ACS.format(i=15, ref=29))
    s1.append(_CAPTURE)
    s1.append(_DSEQ)
    for k in range(5):                       # 18/19 ... 26/27
        s1.append(_VCS.format(i=18 + k * 2, ref=30 + k * 2))
        s1.append(_ACS.format(i=19 + k * 2, ref=31 + k * 2))
    s2 = []
    for k in range(6):                       # 28/29 ... 38/39
        s2.append(_VS.format(i=28 + k * 2))
        s2.append(_AS.format(i=29 + k * 2))
    return "\n".join(s1), "\n".join(s2)


# ---------------------------------------------------------------------------
# 各对象 XML
# ---------------------------------------------------------------------------
def x_clip_project_item(photo, is_seq=False, grid_order=0):
    label = "BE.Prefs.LabelColors.5" if is_seq else "BE.Prefs.LabelColors.3"
    return (
        f'<ClipProjectItem ObjectUID="{photo.clip_guid}" ClassID="cb4e0ed7-aca1-4171-8525-e3658dec06dd" Version="1">\n'
        f'\t<ProjectItem Version="1">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<Column.PropertyText.Label>{label}</Column.PropertyText.Label>\n'
        f'\t\t\t\t<project.icon.view.grid.order>{grid_order}</project.icon.view.grid.order>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<Name>{escape(photo.name)}</Name>\n'
        f'\t</ProjectItem>\n'
        f'\t<MasterClip ObjectURef="{photo.master_guid}"/>\n'
        f'</ClipProjectItem>'
    )


def x_master_clip(photo, clip_ids, is_seq=False):
    clips = "\n".join(
        f'\t\t<Clip Index="{i}" ObjectRef="{cid}"/>'
        for i, cid in enumerate(clip_ids)
    )
    ac = ""
    if is_seq:
        ac = ('\t<AudioComponentChains Version="1">\n'
              f'\t\t<AudioComponentChain Index="0" ObjectRef="{photo.audio_chain_id}"/>\n'
              '\t</AudioComponentChains>\n')
    return (
        f'<MasterClip ObjectUID="{photo.master_guid}" ClassID="fb11c33a-b0a9-4465-aa94-b6d5db2628cf" Version="11">\n'
        f'\t<LoggingInfo ObjectRef="{photo.logging_id}"/>\n'
        f'{ac}'
        f'\t<Clips Version="1">\n'
        f'{clips}\n'
        f'\t</Clips>\n'
        f'\t<AudioClipChannelGroups ObjectRef="{photo.channel_group_id}"/>\n'
        f'\t<Name>{escape(photo.name)}</Name>\n'
        f'\t<OriginatingProjectGuid>00000000-0000-0000-0000-000000000000</OriginatingProjectGuid>\n'
        f'\t<OriginatingMasterClipID>00000000-0000-0000-0000-000000000000</OriginatingMasterClipID>\n'
        f'\t<MasterClipChangeVersion>{"8736" if is_seq else "2"}</MasterClipChangeVersion>\n'
        f'</MasterClip>'
    )


def x_clip_logging(photo, is_seq=False):
    if is_seq:
        return (f'<ClipLoggingInfo ObjectID="{photo.logging_id}" '
                f'ClassID="77ab7fdd-dcdf-465d-9906-7a330ca1e738" Version="8">\n'
                f'\t<MediaFrameRate>9223372036854775807</MediaFrameRate>\n'
                f'</ClipLoggingInfo>')
    return (
        f'<ClipLoggingInfo ObjectID="{photo.logging_id}" '
        f'ClassID="77ab7fdd-dcdf-465d-9906-7a330ca1e738" Version="8">\n'
        f'\t<CaptureMode>2</CaptureMode>\n'
        f'\t<ClipName>{escape(photo.name)}</ClipName>\n'
        f'\t<MediaFrameRate>{SRC_FRAME}</MediaFrameRate>\n'
        f'\t<TimecodeFormat>101</TimecodeFormat>\n'
        f'</ClipLoggingInfo>'
    )


def x_bin_video_clip(alloc, photo):
    return (
        f'<VideoClip ObjectID="{photo.bin_clip_id}" ClassID="9308dbef-2440-4acb-9ab2-953b9a4e82ec" Version="11">\n'
        f'\t<Clip Version="18">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<BE.Prefs.StillImages.DefaultIsDropFrame>false</BE.Prefs.StillImages.DefaultIsDropFrame>\n'
        f'\t\t\t\t<asl.clip.label.color>14910691</asl.clip.label.color>\n'
        f'\t\t\t\t<asl.clip.label.name>BE.Prefs.LabelColors.3</asl.clip.label.name>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<MarkerOwner Version="1">\n'
        f'\t\t\t<Markers ObjectRef="{photo.markers_id}"/>\n'
        f'\t\t</MarkerOwner>\n'
        f'\t\t<Source ObjectRef="{photo.source_id}"/>\n'
        f'\t\t<ClipID>{alloc.uid()}</ClipID>\n'
        f'\t\t<InPoint>0</InPoint>\n'
        f'\t\t<OutPoint>{photo.src_ticks}</OutPoint>\n'
        f'\t\t<InUse>false</InUse>\n'
        f'\t</Clip>\n'
        f'</VideoClip>'
    )


def x_channel_group(photo):
    return (f'<ClipChannelGroupVectorSerializer ObjectID="{photo.channel_group_id}" '
            f'ClassID="a3127a8c-95d4-456e-a7f5-171b3f922426" Version="1">\n'
            f'</ClipChannelGroupVectorSerializer>')


def x_markers(photo):
    return (
        f'<Markers ObjectID="{photo.markers_id}" ClassID="bee50706-b524-416c-9f03-b596ce5f6866" Version="4">\n'
        f'\t<ByGUID>byGUID</ByGUID>\n'
        f'\t<LastMetadataState>{photo.meta_guid}</LastMetadataState>\n'
        f'\t<LastContentState>00000000-0000-0000-0000-000000000000</LastContentState>\n'
        f'</Markers>'
    )


def x_media_source(photo):
    return (
        f'<VideoMediaSource ObjectID="{photo.source_id}" ClassID="e64ddf74-8fac-4682-8aa8-0e0ca2248949" Version="2">\n'
        f'\t<MediaSource Version="4">\n'
        f'\t\t<Content Version="10">\n'
        f'\t\t</Content>\n'
        f'\t\t<Media ObjectURef="{photo.media_guid}"/>\n'
        f'\t</MediaSource>\n'
        f'\t<OriginalDuration>{SRC_ORIGINAL_DURATION}</OriginalDuration>\n'
        f'</VideoMediaSource>'
    )


def x_media(alloc, photo, relpath, abspath):
    body = guid16le_b64(photo.meta_guid)
    return (
        f'<Media ObjectUID="{photo.media_guid}" ClassID="7a5c103e-f3ac-4391-b6b4-7cc3d2f9a7ff" Version="27">\n'
        f'\t<VideoStream ObjectRef="{photo.stream_id}"/>\n'
        f'\t<ModificationState Encoding="base64" BinaryHash="{bin_hash(len(body.encode("utf-16-le")))}">\n'
        f'\t\t{body}\n'
        f'\t</ModificationState>\n'
        f'\t<RelativePath>{escape(relpath)}</RelativePath>\n'
        f'\t<FilePath>{escape(abspath)}</FilePath>\n'
        f'\t<Infinite>true</Infinite>\n'
        f'\t<ImplementationID>1fa18bfa-255c-44b1-ad73-56bcd99fceaf</ImplementationID>\n'
        f'\t<Title>{escape(photo.name)}</Title>\n'
        f'\t<FileKey>{alloc.uid()}</FileKey>\n'
        f'\t<ActualMediaFilePath>{escape(abspath)}</ActualMediaFilePath>\n'
        f'\t<ContentAndMetadataState>{photo.meta_guid}</ContentAndMetadataState>\n'
        f'\t<ConformedAudioRate>9223372036854775807</ConformedAudioRate>\n'
        f'</Media>'
    )


def x_video_stream(photo):
    return (
        f'<VideoStream ObjectID="{photo.stream_id}" ClassID="a36e4719-3ec6-4a0c-ab11-8b4aab377aa5" Version="19">\n'
        f'\t<IsStill>true</IsStill>\n'
        f'\t<SelectedColorSpace>{{}}</SelectedColorSpace>\n'
        f'\t<OverriddenColorSpace>{{}}</OverriddenColorSpace>\n'
        f'\t<InputLUTSpecified>false</InputLUTSpecified>\n'
        f'\t<InputLUTID>00000000-0000-0000-0000-000000000000</InputLUTID>\n'
        f'\t<FrameRate>{SRC_FRAME}</FrameRate>\n'
        f'\t<FrameRect>0,0,{photo.w},{photo.h}</FrameRect>\n'
        f'\t<PARIsUncertain>true</PARIsUncertain>\n'
        f'\t<Duration>{MEDIA_DURATION}</Duration>\n'
        f'\t<CodecType>1785750887</CodecType>\n'
        f'\t<FieldTypeIsUncertain>true</FieldTypeIsUncertain>\n'
        f'</VideoStream>'
    )


def x_seq_logging(seq):
    return (f'<ClipLoggingInfo ObjectID="{seq.logging_id}" '
            f'ClassID="77ab7fdd-dcdf-465d-9906-7a330ca1e738" Version="8">\n'
            f'\t<MediaFrameRate>9223372036854775807</MediaFrameRate>\n'
            f'</ClipLoggingInfo>')


def x_seq_audio_chain(seq):
    return (
        f'<AudioComponentChain ObjectID="{seq.audio_chain_id}" ClassID="3cb131d1-d3c0-47ae-a19a-bdf75ea11674" Version="3">\n'
        f'\t<ComponentChain Version="3">\n'
        f'\t</ComponentChain>\n'
        f'\t<DefaultVol>true</DefaultVol>\n'
        f'\t<DefaultVolumeComponentID>1</DefaultVolumeComponentID>\n'
        f'\t<DefaultChannelVolumeComponentID>2</DefaultChannelVolumeComponentID>\n'
        f'\t<ChannelType>1</ChannelType>\n'
        f'\t<FrameRate>5760000</FrameRate>\n'
        f'\t<AutomationMode>1</AutomationMode>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioComponentChain>'
    )


def x_seq_audio_clip(alloc, seq):
    return (
        f'<AudioClip ObjectID="{seq.bin_clip_ids[0]}" ClassID="b8830d03-de02-41ee-84ec-fe566dc70cd9" Version="8">\n'
        f'\t<Clip Version="18">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<asl.clip.label.color>5814353</asl.clip.label.color>\n'
        f'\t\t\t\t<asl.clip.label.name>BE.Prefs.LabelColors.5</asl.clip.label.name>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<Source ObjectRef="{seq.audio_source_id}"/>\n'
        f'\t\t<ClipID>{alloc.uid()}</ClipID>\n'
        f'\t\t<InUse>false</InUse>\n'
        f'\t</Clip>\n'
        f'\t<SecondaryContents Version="1">\n'
        f'\t\t<SecondaryContentItem Index="0" ObjectRef="{seq.sec1_id}"/>\n'
        f'\t\t<SecondaryContentItem Index="1" ObjectRef="{seq.sec2_id}"/>\n'
        f'\t</SecondaryContents>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioClip>'
    )


def x_seq_video_clip(alloc, seq):
    return (
        f'<VideoClip ObjectID="{seq.bin_clip_ids[1]}" ClassID="9308dbef-2440-4acb-9ab2-953b9a4e82ec" Version="11">\n'
        f'\t<Clip Version="18">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<asl.clip.label.color>5814353</asl.clip.label.color>\n'
        f'\t\t\t\t<asl.clip.label.name>BE.Prefs.LabelColors.5</asl.clip.label.name>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<Source ObjectRef="{seq.video_source_id}"/>\n'
        f'\t\t<ClipID>{alloc.uid()}</ClipID>\n'
        f'\t\t<InUse>false</InUse>\n'
        f'\t</Clip>\n'
        f'</VideoClip>'
    )


def x_seq_channel_group(seq):
    return (
        f'<ClipChannelGroupVectorSerializer ObjectID="{seq.channel_group_id}" '
        f'ClassID="a3127a8c-95d4-456e-a7f5-171b3f922426" Version="1">\n'
        f'\t<ClipChannelVectors Version="1">\n'
        f'\t\t<ClipChannelVectorItem Index="0" ObjectRef="{seq.channel_vec_id}"/>\n'
        f'\t</ClipChannelVectors>\n'
        f'</ClipChannelGroupVectorSerializer>'
    )


def x_seq_audio_source(seq):
    return (
        f'<AudioSequenceSource ObjectID="{seq.audio_source_id}" ClassID="e8d4cc83-38cb-491f-9d94-e5f7e3b205ee" Version="7">\n'
        f'\t<SequenceSource Version="4">\n'
        f'\t\t<Content Version="10">\n'
        f'\t\t</Content>\n'
        f'\t\t<Sequence ObjectURef="{seq.sequence_guid}"/>\n'
        f'\t</SequenceSource>\n'
        f'\t<OriginalDuration>{seq.total}</OriginalDuration>\n'
        f'</AudioSequenceSource>'
    )


def x_seq_sec_content(seq, sid, ch):
    return (
        f'<SecondaryContent ObjectID="{sid}" ClassID="f9d004b5-cb04-4e2f-af6f-64fadc2c4be9" Version="1">\n'
        f'\t<Content ObjectRef="{seq.audio_source_id}"/>\n'
        f'\t<ChannelIndex>{ch}</ChannelIndex>\n'
        f'</SecondaryContent>'
    )


def x_seq_video_source(seq):
    return (
        f'<VideoSequenceSource ObjectID="{seq.video_source_id}" ClassID="4752dfa9-7a7e-4a3b-a25b-cafde1a8d036" Version="3">\n'
        f'\t<SequenceSource Version="4">\n'
        f'\t\t<Content Version="10">\n'
        f'\t\t</Content>\n'
        f'\t\t<Sequence ObjectURef="{seq.sequence_guid}"/>\n'
        f'\t</SequenceSource>\n'
        f'\t<OriginalDuration>{seq.total}</OriginalDuration>\n'
        f'</VideoSequenceSource>'
    )


def x_seq_channel_vec(seq):
    return (
        f'<ClipChannelVectorSerializer ObjectID="{seq.channel_vec_id}" ClassID="333d203b-3a53-4195-8894-fc7523ff3dc7" Version="1">\n'
        f'\t<ClipChannels Version="1">\n'
        f'\t\t<ClipChannelItem Index="0" ObjectRef="{seq.ch0_id}"/>\n'
        f'\t\t<ClipChannelItem Index="1" ObjectRef="{seq.ch1_id}"/>\n'
        f'\t</ClipChannels>\n'
        f'\t<ChannelType>1</ChannelType>\n'
        f'</ClipChannelVectorSerializer>'
    )


def x_seq_channel_serializer(seq, cid, ch):
    return (
        f'<ClipChannelSerializer ObjectID="{cid}" ClassID="5c89aa7a-89a6-4483-becd-f2b1def42316" Version="1">\n'
        f'\t<SourceClipIndex>0</SourceClipIndex>\n'
        f'\t<mSourceChannelIndex>{ch}</mSourceChannelIndex>\n'
        f'</ClipChannelSerializer>'
    )


# ---------------------------------------------------------------------------
# 背景音乐
# ---------------------------------------------------------------------------
AUDIO_TB = 5292000            # 音频轨道刻度（48kHz × 110.25，同示例）
AUDIO_VOL = 0.17782793939113617   # 基础音量 ≈ -15dB（示例值）
AUDIO_TS = [80000000000000]   # 音频参数 Timestamp 模拟（递增，无实际语义）

def _ts():
    AUDIO_TS[0] += 3500
    return AUDIO_TS[0]


class AudioTrack:
    """一个音频文件（如某首曲的 Intro/Main 段）：独立的素材库对象 + 该文件在
    时间线上的播放段（同一文件被循环播放时产生多段，复用同一套素材库）。"""
    def __init__(self, name, path, dur_sec):
        self.name = name
        self.path = path
        self.dur_sec = dur_sec
        self.dur_ticks = round(dur_sec * SEQ_TB)
        self.clip_guid = str(uuid.uuid4())
        self.master_guid = str(uuid.uuid4())
        self.media_guid = str(uuid.uuid4())
        self.meta_guid = str(uuid.uuid4())
        # 素材库对象 ID —— build() 分配
        self.logging_id = None
        self.bin_chain_id = None
        self.bin_clip_id = None
        self.channel_group_id = None
        self.markers_id = None
        self.source_id = None
        self.sec1_id = None
        self.sec2_id = None
        self.stream_id = None
        self.channel_vec_id = None
        self.ch0_id = None
        self.ch1_id = None
        # 该文件在时间线上的播放段（帧对齐；同一文件循环多次时列表变长）
        self.seg_item_id = []
        self.seg_chain_id = []
        self.seg_subclip_id = []
        self.seg_clip_id = []
        self.seg_starts = []
        self.seg_ends = []


class AudioMusic:
    """背景音乐系统：多首曲目（每首可含 Intro+Main 两段）依次播放，
    全部播完仍不够覆盖视频时从头循环；结尾最后一个播放段挂音量渐弱滤镜。"""
    def __init__(self, tracks, fade_ticks):
        self.tracks = tracks                  # list[AudioTrack]，素材库发射顺序
        self.fade_ticks = fade_ticks
        self.seg_plan = []                    # 时间线播放计划 [(track_idx, seg_idx)]
        self.seg_starts = []                  # 全局各段 Start
        self.seg_ends = []                    # 全局各段 End
        self.n_seg = 0
        self.last_track = None                # 全局最后一段所属 track 引用
        self.last_seg_idx = None
        # 渐弱滤镜（挂在全局最后一段的组件链上）
        self.vol_filter_id = None
        self.ch_filter_id = None
        self.vol_bypass_id = None
        self.vol_level_id = None
        self.ch_bypass_id = None
        self.ch_left_id = None
        self.ch_right_id = None
        self.ch_zero_ids = [None] * 30


def build_audio_plan(music, total):
    """按曲目顺序把各文件依次排入时间线；总长不足则从头循环，直到覆盖 total。
    段时长 = 文件完整时长（帧对齐向上取整），全局最后一段截到 total。"""
    pos = 0
    n_tracks = len(music.tracks)
    while pos < total:
        for ti, t in enumerate(music.tracks):
            seg_ticks = max(1, round(t.dur_ticks / SEQ_FRAME)) * SEQ_FRAME
            start, end = pos, min(pos + seg_ticks, total)
            si = len(t.seg_starts)
            t.seg_starts.append(start)
            t.seg_ends.append(end)
            t.seg_item_id.append(None)
            t.seg_chain_id.append(None)
            t.seg_subclip_id.append(None)
            t.seg_clip_id.append(None)
            music.seg_plan.append((ti, si))
            music.seg_starts.append(start)
            music.seg_ends.append(end)
            music.n_seg += 1
            pos = end
            if pos >= total:
                break
        if n_tracks == 0:
            break
    if music.n_seg:
        ti, si = music.seg_plan[-1]
        music.last_track = music.tracks[ti]
        music.last_seg_idx = si


def aac_duration(path):
    """ADTS-AAC 时长（秒）。解析帧头统计帧数 × 1024 采样 / 采样率。"""
    with open(path, "rb") as f:
        data = f.read()
    i, n, frames = 0, len(data), 0
    sr_idx = 0
    while i + 7 < n:
        if data[i] == 0xFF and (data[i + 1] & 0xF0) == 0xF0:
            sr_idx = (data[i + 2] >> 2) & 0x0F
            fl = ((data[i + 3] & 0x03) << 11) | (data[i + 4] << 3) | \
                 ((data[i + 5] >> 5) & 0x07)
            if fl <= 0:
                break
            frames += 1
            i += fl
        else:
            i += 1
    if frames == 0:
        return None
    rates = [96000, 88200, 64000, 48000, 44100, 32000, 24000,
             22050, 16000, 12000, 11025, 8000, 7350]
    sr = rates[sr_idx] if sr_idx < len(rates) else 44100
    return frames * 1024.0 / sr


def x_audio_logging(t):
    return (
        f'<ClipLoggingInfo ObjectID="{t.logging_id}" '
        f'ClassID="77ab7fdd-dcdf-465d-9906-7a330ca1e738" Version="8">\n'
        f'\t<CaptureMode>1</CaptureMode>\n'
        f'\t<ClipName>{escape(t.name)}</ClipName>\n'
        f'\t<MediaInPoint>0</MediaInPoint>\n'
        f'\t<MediaOutPoint>{t.dur_ticks}</MediaOutPoint>\n'
        f'\t<MediaFrameRate>{AUDIO_TB}</MediaFrameRate>\n'
        f'\t<TimecodeFormat>200</TimecodeFormat>\n'
        f'</ClipLoggingInfo>'
    )


def x_audio_bin_chain(t):
    return (
        f'<AudioComponentChain ObjectID="{t.bin_chain_id}" '
        f'ClassID="3cb131d1-d3c0-47ae-a19a-bdf75ea11674" Version="3">\n'
        f'\t<ComponentChain Version="3">\n'
        f'\t</ComponentChain>\n'
        f'\t<DefaultVol>true</DefaultVol>\n'
        f'\t<DefaultVolumeComponentID>1</DefaultVolumeComponentID>\n'
        f'\t<DefaultChannelVolumeComponentID>2</DefaultChannelVolumeComponentID>\n'
        f'\t<ChannelType>1</ChannelType>\n'
        f'\t<FrameRate>{AUDIO_TB}</FrameRate>\n'
        f'\t<AutomationMode>1</AutomationMode>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioComponentChain>'
    )


def x_audio_bin_clip(alloc, t):
    return (
        f'<AudioClip ObjectID="{t.bin_clip_id}" '
        f'ClassID="b8830d03-de02-41ee-84ec-fe566dc70cd9" Version="8">\n'
        f'\t<Clip Version="18">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<asl.clip.label.color>10016297</asl.clip.label.color>\n'
        f'\t\t\t\t<asl.clip.label.name>BE.Prefs.LabelColors.2</asl.clip.label.name>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<MarkerOwner Version="1">\n'
        f'\t\t\t<Markers ObjectRef="{t.markers_id}"/>\n'
        f'\t\t</MarkerOwner>\n'
        f'\t\t<Source ObjectRef="{t.source_id}"/>\n'
        f'\t\t<ClipID>{alloc.uid()}</ClipID>\n'
        f'\t\t<InUse>false</InUse>\n'
        f'\t</Clip>\n'
        f'\t<SecondaryContents Version="1">\n'
        f'\t\t<SecondaryContentItem Index="0" ObjectRef="{t.sec1_id}"/>\n'
        f'\t\t<SecondaryContentItem Index="1" ObjectRef="{t.sec2_id}"/>\n'
        f'\t</SecondaryContents>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioClip>'
    )


def x_audio_channel_group(t):
    return (
        f'<ClipChannelGroupVectorSerializer ObjectID="{t.channel_group_id}" '
        f'ClassID="a3127a8c-95d4-456e-a7f5-171b3f922426" Version="1">\n'
        f'\t<ClipChannelVectors Version="1">\n'
        f'\t\t<ClipChannelVectorItem Index="0" ObjectRef="{t.channel_vec_id}"/>\n'
        f'\t</ClipChannelVectors>\n'
        f'</ClipChannelGroupVectorSerializer>'
    )


def x_audio_markers(t):
    return (
        f'<Markers ObjectID="{t.markers_id}" ClassID="bee50706-b524-416c-9f03-b596ce5f6866" Version="4">\n'
        f'\t<ByGUID>byGUID</ByGUID>\n'
        f'\t<LastMetadataState>{t.meta_guid}</LastMetadataState>\n'
        f'\t<LastContentState>00000000-0000-0000-0000-000000000000</LastContentState>\n'
        f'</Markers>'
    )


def x_audio_media_source(t):
    return (
        f'<AudioMediaSource ObjectID="{t.source_id}" '
        f'ClassID="f588da05-fc2a-4fbc-9383-74d653b379e3" Version="2">\n'
        f'\t<MediaSource Version="4">\n'
        f'\t\t<Content Version="10">\n'
        f'\t\t</Content>\n'
        f'\t\t<Media ObjectURef="{t.media_guid}"/>\n'
        f'\t</MediaSource>\n'
        f'\t<OriginalDuration>{t.dur_ticks}</OriginalDuration>\n'
        f'</AudioMediaSource>'
    )


def x_audio_sec_content(t, sid, ch):
    return (
        f'<SecondaryContent ObjectID="{sid}" '
        f'ClassID="f9d004b5-cb04-4e2f-af6f-64fadc2c4be9" Version="1">\n'
        f'\t<Content ObjectRef="{t.source_id}"/>\n'
        f'\t<ChannelIndex>{ch}</ChannelIndex>\n'
        f'</SecondaryContent>'
    )


def x_audio_channel_vec(t):
    return (
        f'<ClipChannelVectorSerializer ObjectID="{t.channel_vec_id}" '
        f'ClassID="333d203b-3a53-4195-8894-fc7523ff3dc7" Version="1">\n'
        f'\t<ClipChannels Version="1">\n'
        f'\t\t<ClipChannelItem Index="0" ObjectRef="{t.ch0_id}"/>\n'
        f'\t\t<ClipChannelItem Index="1" ObjectRef="{t.ch1_id}"/>\n'
        f'\t</ClipChannels>\n'
        f'\t<ChannelType>1</ChannelType>\n'
        f'</ClipChannelVectorSerializer>'
    )


def x_audio_channel_item(t, cid, ch):
    return (
        f'<ClipChannelSerializer ObjectID="{cid}" '
        f'ClassID="5c89aa7a-89a6-4483-becd-f2b1def42316" Version="1">\n'
        f'\t<SourceClipIndex>0</SourceClipIndex>\n'
        f'\t<mSourceChannelIndex>{ch}</mSourceChannelIndex>\n'
        f'</ClipChannelSerializer>'
    )


def x_audio_stream(t):
    return (
        f'<AudioStream ObjectID="{t.stream_id}" '
        f'ClassID="0b5cf52f-2b85-4863-890b-8844b64ecfe9" Version="7">\n'
        f'\t<FrameRate>{AUDIO_TB}</FrameRate>\n'
        f'\t<SampleType>7</SampleType>\n'
        f'\t<Duration>{t.dur_ticks}</Duration>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioStream>'
    )


def x_audio_media(alloc, t, relpath, abspath):
    body = guid16le_b64(t.meta_guid)
    return (
        f'<Media ObjectUID="{t.media_guid}" ClassID="7a5c103e-f3ac-4391-b6b4-7cc3d2f9a7ff" Version="27">\n'
        f'\t<AudioStream ObjectRef="{t.stream_id}"/>\n'
        f'\t<ModificationState Encoding="base64" BinaryHash="{bin_hash(len(body.encode("utf-16-le")))}">\n'
        f'\t\t{body}\n'
        f'\t</ModificationState>\n'
        f'\t<RelativePath>{escape(relpath)}</RelativePath>\n'
        f'\t<FilePath>{escape(abspath)}</FilePath>\n'
        f'\t<ImplementationID>1fa18bfa-255c-44b1-ad73-56bcd99fceaf</ImplementationID>\n'
        f'\t<Title>{escape(t.name)}</Title>\n'
        f'\t<FileKey>{alloc.uid()}</FileKey>\n'
        f'\t<ActualMediaFilePath>{escape(abspath)}</ActualMediaFilePath>\n'
        f'\t<ContentAndMetadataState>{t.meta_guid}</ContentAndMetadataState>\n'
        f'\t<ConformedAudioRate>{AUDIO_TB}</ConformedAudioRate>\n'
        f'</Media>'
    )


def x_audio_clip_project_item(t):
    return (
        f'<ClipProjectItem ObjectUID="{t.clip_guid}" '
        f'ClassID="cb4e0ed7-aca1-4171-8525-e3658dec06dd" Version="1">\n'
        f'\t<ProjectItem Version="1">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<Column.PropertyText.Label>BE.Prefs.LabelColors.2</Column.PropertyText.Label>\n'
        f'\t\t\t\t<project.icon.view.grid.order>1</project.icon.view.grid.order>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<Name>{escape(t.name)}</Name>\n'
        f'\t</ProjectItem>\n'
        f'\t<MasterClip ObjectURef="{t.master_guid}"/>\n'
        f'</ClipProjectItem>'
    )


def x_audio_master_clip(t):
    return (
        f'<MasterClip ObjectUID="{t.master_guid}" '
        f'ClassID="fb11c33a-b0a9-4465-aa94-b6d5db2628cf" Version="11">\n'
        f'\t<LoggingInfo ObjectRef="{t.logging_id}"/>\n'
        f'\t<AudioComponentChains Version="1">\n'
        f'\t\t<AudioComponentChain Index="0" ObjectRef="{t.bin_chain_id}"/>\n'
        f'\t</AudioComponentChains>\n'
        f'\t<Clips Version="1">\n'
        f'\t\t<Clip Index="0" ObjectRef="{t.bin_clip_id}"/>\n'
        f'\t</Clips>\n'
        f'\t<AudioClipChannelGroups ObjectRef="{t.channel_group_id}"/>\n'
        f'\t<Name>{escape(t.name)}</Name>\n'
        f'\t<DefMappingID>{t.meta_guid}</DefMappingID>\n'
        f'\t<OriginatingProjectGuid>00000000-0000-0000-0000-000000000000</OriginatingProjectGuid>\n'
        f'\t<OriginatingMasterClipID>00000000-0000-0000-0000-000000000000</OriginatingMasterClipID>\n'
        f'\t<MasterClipChangeVersion>2</MasterClipChangeVersion>\n'
        f'</MasterClip>'
    )


def x_audio_seg_chain(t, seg_idx, last, vol_ref, ch_ref):
    """每段音频自己的组件链；全局最后一段挂音量/通道音量滤镜。"""
    comp = ""
    if last:
        comp = (
            f'\t\t<Components Version="1">\n'
            f'\t\t\t<Component Index="0" ObjectRef="{vol_ref}"/>\n'
            f'\t\t\t<Component Index="1" ObjectRef="{ch_ref}"/>\n'
            f'\t\t</Components>\n'
        )
    default_vol = "" if last else (
        f'\t<DefaultVol>true</DefaultVol>\n'
        f'\t<DefaultVolumeComponentID>1</DefaultVolumeComponentID>\n'
        f'\t<DefaultChannelVolumeComponentID>2</DefaultChannelVolumeComponentID>\n'
    )
    return (
        f'<AudioComponentChain ObjectID="{t.seg_chain_id[seg_idx]}" '
        f'ClassID="3cb131d1-d3c0-47ae-a19a-bdf75ea11674" Version="3">\n'
        f'\t<ComponentChain Version="3">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<MZ.ComponentChain.ActiveComponentID>1</MZ.ComponentChain.ActiveComponentID>\n'
        f'\t\t\t\t<MZ.ComponentChain.ActiveComponentParamIndex>4294967295</MZ.ComponentChain.ActiveComponentParamIndex>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'{comp}'
        f'\t</ComponentChain>\n'
        f'{default_vol}'
        f'\t<ChannelType>1</ChannelType>\n'
        f'\t<FrameRate>{AUDIO_TB}</FrameRate>\n'
        f'\t<AutomationMode>1</AutomationMode>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioComponentChain>'
    )


def x_audio_clip(alloc, t, seg_idx, in_pt, out_pt):
    return (
        f'<AudioClip ObjectID="{t.seg_clip_id[seg_idx]}" '
        f'ClassID="b8830d03-de02-41ee-84ec-fe566dc70cd9" Version="8">\n'
        f'\t<Clip Version="18">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<asl.clip.label.name>BE.Prefs.LabelColors.2</asl.clip.label.name>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<MarkerOwner Version="1">\n'
        f'\t\t\t<Markers ObjectRef="{t.markers_id}"/>\n'
        f'\t\t</MarkerOwner>\n'
        f'\t\t<Source ObjectRef="{t.source_id}"/>\n'
        f'\t\t<ClipID>{alloc.uid()}</ClipID>\n'
        f'\t\t<InPoint>{in_pt}</InPoint>\n'
        f'\t\t<OutPoint>{out_pt}</OutPoint>\n'
        f'\t</Clip>\n'
        f'\t<SecondaryContents Version="1">\n'
        f'\t\t<SecondaryContentItem Index="0" ObjectRef="{t.sec1_id}"/>\n'
        f'\t\t<SecondaryContentItem Index="1" ObjectRef="{t.sec2_id}"/>\n'
        f'\t</SecondaryContents>\n'
        f'\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'</AudioClip>'
    )


def x_audio_subclip(t, seg_idx):
    return (
        f'<SubClip ObjectID="{t.seg_subclip_id[seg_idx]}" '
        f'ClassID="e0c58dc9-dbdd-4166-aef7-5db7e3f22e84" Version="5">\n'
        f'\t<Clip ObjectRef="{t.seg_clip_id[seg_idx]}"/>\n'
        f'\t<MasterClip ObjectURef="{t.master_guid}"/>\n'
        f'\t<Name>{escape(t.name)}</Name>\n'
        f'\t<OrigChGrp>0</OrigChGrp>\n'
        f'</SubClip>'
    )


def x_audio_clip_track_item(alloc, t, seg_idx):
    return (
        f'<AudioClipTrackItem ObjectID="{t.seg_item_id[seg_idx]}" '
        f'ClassID="064ec682-9ba6-11d5-af2d-9ca32c7d6164" Version="6">\n'
        f'\t<ClipTrackItem Version="8">\n'
        f'\t\t<ComponentOwner Version="1">\n'
        f'\t\t\t<Components ObjectRef="{t.seg_chain_id[seg_idx]}"/>\n'
        f'\t\t</ComponentOwner>\n'
        f'\t\t<TrackItem Version="3">\n'
        f'\t\t\t<Start>{t.seg_starts[seg_idx]}</Start>\n'
        f'\t\t\t<End>{t.seg_ends[seg_idx]}</End>\n'
        f'\t\t</TrackItem>\n'
        f'\t\t<SubClip ObjectRef="{t.seg_subclip_id[seg_idx]}"/>\n'
        f'\t</ClipTrackItem>\n'
        f'\t<ID>{alloc.uid()}</ID>\n'
        f'</AudioClipTrackItem>'
    )


def audio_filter_component_audio(alloc, comp_id, param_xmls, fid, display, match):
    params = "\n".join(
        f'\t\t\t<Param Index="{i}" ObjectRef="{pid_of(p)}"/>'
        for i, p in enumerate(param_xmls)
    )
    return (
        f'<AudioFilterComponent ObjectID="{comp_id}" '
        f'ClassID="d77a90a0-6c9e-44bf-9b20-de8c21168fe1" Version="3">\n'
        f'\t<AudioComponent Version="3">\n'
        f'\t\t<Component Version="6">\n'
        f'\t\t\t<Params Version="1">\n'
        f'{params}\n'
        f'\t\t\t</Params>\n'
        f'\t\t\t<ID>{fid}</ID>\n'
        f'\t\t\t<DisplayName>{escape(display)}</DisplayName>\n'
        f'\t\t\t<Bypass>false</Bypass>\n'
        f'\t\t\t<Intrinsic>true</Intrinsic>\n'
        f'\t\t\t<ArchivedType>0</ArchivedType>\n'
        f'\t\t</Component>\n'
        f'\t\t<AudioComponentType>0</AudioComponentType>\n'
        f'\t\t<FrameRate>{AUDIO_TB}</FrameRate>\n'
        f'\t\t<ChannelType>1</ChannelType>\n'
        f'\t\t<AudioChannelLayout>[{{"channellabel":100}},{{"channellabel":101}}]</AudioChannelLayout>\n'
        f'\t</AudioComponent>\n'
        f'\t<FilterMatchName>{match}</FilterMatchName>\n'
        f'\t<FilterIndex>-1</FilterIndex>\n'
        f'\t<FilterPreset>0</FilterPreset>\n'
        f'\t<ChannelConfigData>{{"in":[{{"layout":[100,101],"name":"立体声放大","type":0}}],'
        f'"out":[{{"layout":[100,101],"name":"立体声缩小","type":0}}]}}</ChannelConfigData>\n'
        f'</AudioFilterComponent>'
    )


def param_audio_bypass(alloc, oid):
    return (
        f'<AudioComponentParam ObjectID="{oid}" '
        f'ClassID="32657501-3aa4-445f-a49b-d09ecb9fa1ae" Version="9">\n'
        f'\t<Name>旁路</Name>\n'
        f'\t<ParameterControlType>4</ParameterControlType>\n'
        f'\t<Timestamp>{_ts()}</Timestamp>\n'
        f'</AudioComponentParam>'
    )


def param_audio_level(alloc, oid, seg_dur, fade_ticks):
    """音量"级别"参数：结尾渐弱关键帧（片段内时间，参考示例格式）。"""
    kf0 = max(seg_dur - fade_ticks, 0)
    kf1 = seg_dur
    slope = -AUDIO_VOL / max(fade_ticks / SEQ_TB, 1e-6)
    keyframes = (f'{kf0},{fmt_kf(AUDIO_VOL)},0,0,0,0.16666666666666666,{fmt_kf(slope)},0.16666666666666666;'
                 f'{kf1},0.,0,0,{fmt_kf(slope)},0.16666666666666666,0,0.16666666666666666;')
    return (
        f'<AudioComponentParam ObjectID="{oid}" '
        f'ClassID="a714635e-a628-4b27-9d59-77eba47dbc1a" Version="9">\n'
        f'\t<Node Version="1">\n'
        f'\t\t<Properties Version="1">\n'
        f'\t\t\t<ECP.Slider.Expanded>true</ECP.Slider.Expanded>\n'
        f'\t\t</Properties>\n'
        f'\t</Node>\n'
        f'\t<Name>级别</Name>\n'
        f'\t<UnitsString>dB</UnitsString>\n'
        f'\t<ParameterControlType>2</ParameterControlType>\n'
        f'\t<RangeLocked>true</RangeLocked>\n'
        f'\t<Timestamp>{_ts()}</Timestamp>\n'
        f'\t<StartKeyframe>-91445760000000000,{fmt_kf(AUDIO_VOL)},0,0,0,0,0,0</StartKeyframe>\n'
        f'\t<Keyframes>{keyframes}</Keyframes>\n'
        f'\t<CurrentValue>{fmt_kf(AUDIO_VOL)}</CurrentValue>\n'
        f'</AudioComponentParam>'
    )


def param_audio_ch(alloc, oid, name):
    return (
        f'<AudioComponentParam ObjectID="{oid}" '
        f'ClassID="a714635e-a628-4b27-9d59-77eba47dbc1a" Version="9">\n'
        f'\t<Name>{escape(name)}</Name>\n'
        f'\t<UnitsString>dB</UnitsString>\n'
        f'\t<ParameterControlType>2</ParameterControlType>\n'
        f'\t<RangeLocked>true</RangeLocked>\n'
        f'\t<Timestamp>{_ts()}</Timestamp>\n'
        f'\t<StartKeyframe>-91445760000000000,{fmt_kf(AUDIO_VOL)},0,0,0,0,0,0</StartKeyframe>\n'
        f'\t<CurrentValue>{fmt_kf(AUDIO_VOL)}</CurrentValue>\n'
        f'</AudioComponentParam>'
    )


def param_audio_zero(alloc, oid):
    return (
        f'<AudioComponentParam ObjectID="{oid}" '
        f'ClassID="a714635e-a628-4b27-9d59-77eba47dbc1a" Version="9">\n'
        f'\t<UnitsString>dB</UnitsString>\n'
        f'\t<ParameterControlType>2</ParameterControlType>\n'
        f'\t<RangeLocked>true</RangeLocked>\n'
        f'\t<Timestamp>{_ts()}</Timestamp>\n'
        f'\t<StartKeyframe>-91445760000000000,0.,0,0,0,0,0,0</StartKeyframe>\n'
        f'\t<CurrentValue>0</CurrentValue>\n'
        f'</AudioComponentParam>'
    )


def x_sequence(seq, total, track_bg_guid, track_fg_guid):
    props = [
        ("AMM.CurrentSolo", "[]"),
        ("HSL.TimelinePatchingAndTargeting.AudioPatches405230c6_45_7438_45_1002_45_93de_45_aac30000000f",
         '[{"mNumber":0,"mState":0},{"mNumber":-1,"mState":0},{"mNumber":-1,"mState":0},{"mNumber":-1,"mState":0}]'),
        ("HSL.TimelinePatchingAndTargeting.DataPatches405230c6_45_7438_45_1002_45_93de_45_aac30000000f", "[]"),
        ("HSL.TimelinePatchingAndTargeting.VideoPatches4b7f66de_45_1bb0_45_cba9_45_abba_45_e67900000017",
         '[{"mNumber":-1,"mState":0},{"mNumber":0,"mState":2},{"mNumber":-1,"mState":0},{"mNumber":-1,"mState":0}]'),
        ("MZ.EditLine", "0"),
        ("MZ.Sequence.AudioTimeDisplayFormat", "200"),
        ("MZ.Sequence.EditingModeGUID", "9678af98-a7b7-4bdb-b477-7ac9c8df4a4e"),
        ("MZ.Sequence.PreviewFrameSizeHeight", "1080"),
        ("MZ.Sequence.PreviewFrameSizeWidth", "1920"),
        ("MZ.Sequence.PreviewRenderingClassID", "1297106761"),
        ("MZ.Sequence.PreviewRenderingPresetCodec", "1297107278"),
        ("MZ.Sequence.PreviewRenderingPresetPath",
         "EncoderPresets\\SequencePreview\\9678af98-a7b7-4bdb-b477-7ac9c8df4a4e\\I-Frame Only MPEG.epr"),
        ("MZ.Sequence.PreviewUseMaxBitDepth", "false"),
        ("MZ.Sequence.PreviewUseMaxRenderQuality", "false"),
        ("MZ.Sequence.VideoTimeDisplayFormat", "104"),
        ("MZ.WorkInPoint", "0"),
        ("MZ.WorkOutPoint", str(total)),
        ("Monitor.ProgramZoomIn", "0"),
        ("Monitor.ProgramZoomOut", str(total)),
        ("Monitor.SourceAndProgramGangState", "0"),
        ("TL.SQAVDividerPosition", "0.5"),
        ("TL.SQAudioVisibleBase", "3"),
        ("TL.SQDataTrackViewControlState", "0"),
        ("TL.SQDataVisibleBase", "0"),
        ("TL.SQHeaderWidth", "236"),
        ("TL.SQHideShyTracks", "0"),
        ("TL.SQTimePerPixel", "0.066498845460436579"),
        ("TL.SQVideoVisibleBase", "0"),
        ("TL.SQVisibleBaseTime", "0"),
    ]
    prop_xml = "\n".join(f'\t\t\t\t<{k}>{escape(str(v))}</{k}>' for k, v in props)
    return (
        f'<Sequence ObjectUID="{seq.sequence_guid}" ClassID="6a15d903-8739-11d5-af2d-9b7855ad8974" Version="11">\n'
        f'\t<Node Version="1">\n'
        f'\t\t<Properties Version="1">\n'
        f'{prop_xml}\n'
        f'\t\t</Properties>\n'
        f'\t</Node>\n'
        f'\t<PersistentGroupContainer Version="1">\n'
        f'\t\t<LinkContainer Version="1">\n'
        f'\t\t</LinkContainer>\n'
        f'\t</PersistentGroupContainer>\n'
        f'\t<TrackGroups Version="1">\n'
        f'\t\t<TrackGroup Version="1" Index="0">\n'
        f'\t\t\t<First>228cda18-3625-4d2d-951e-348879e4ed93</First>\n'
        f'\t\t\t<Second ObjectRef="100"/>\n'
        f'\t\t</TrackGroup>\n'
        f'\t\t<TrackGroup Version="1" Index="1">\n'
        f'\t\t\t<First>80b8e3d5-6dca-4195-aefb-cb5f407ab009</First>\n'
        f'\t\t\t<Second ObjectRef="101"/>\n'
        f'\t\t</TrackGroup>\n'
        f'\t\t<TrackGroup Version="1" Index="2">\n'
        f'\t\t\t<First>d8143ffe-eec4-4d2a-a909-d5f7bf094dc5</First>\n'
        f'\t\t\t<Second ObjectRef="102"/>\n'
        f'\t\t</TrackGroup>\n'
        f'\t</TrackGroups>\n'
        f'\t<ID>1</ID>\n'
        f'\t<Name>{escape(seq.name)}</Name>\n'
        f'\t<PreviewFormatIdentifier>b0f75bf9-a1fa-f37f-f0e2-3a24000000fa</PreviewFormatIdentifier>\n'
        f'</Sequence>'
    )


def x_video_track_group(w, h, track_guids):
    """VideoTrackGroup#100：4 条视频轨道（bg/fg/两个空轨），与示例一致。"""
    tracks = "\n".join(
        f'\t\t\t<Track Index="{i}" ObjectURef="{g}"/>'
        for i, g in enumerate(track_guids)
    )
    return (
        f'<VideoTrackGroup ObjectID="100" ClassID="9e9abf7a-0918-49c2-91ae-991b5dde77bb" Version="12">\n'
        f'\t<TrackGroup Version="1">\n'
        f'\t\t<Tracks Version="1">\n'
        f'{tracks}\n'
        f'\t\t</Tracks>\n'
        f'\t\t<FrameRate>{SEQ_FRAME}</FrameRate>\n'
        f'\t\t<NextTrackID>5</NextTrackID>\n'
        f'\t</TrackGroup>\n'
        f'\t<FrameRect>0,0,{w},{h}</FrameRect>\n'
        f'\t<PixelAspectRatio>1,1</PixelAspectRatio>\n'
        f'\t<FieldType>0</FieldType>\n'
        f'\t<AllowLinearCompositing>true</AllowLinearCompositing>\n'
        f'\t<ImmersiveVideoVRConfiguration>{{"ambisonicsHRIR":"","ambisonicsMonitoringType":0,"capturedHorizontalView":0,"capturedVerticalView":0,"fieldOfHorizontalView":108,"fieldOfVerticalView":108,"projectionType":0,"stereoscopicEye":0,"stereoscopicType":0,"version":3}}</ImmersiveVideoVRConfiguration>\n'
        f'\t<WorkingColorSpaceConfiguration>{{"workingSpaceConfigVersion":1,"workingSpaceID":"BT.709 RGB Full","workingSpaceIsLinearized":0}}</WorkingColorSpaceConfiguration>\n'
        f'\t<WorkingColorSpace>{{"baseColorProfile":{{"colorProfileName":"BT.709 RGB Full"}},"baseProfileType":1}}</WorkingColorSpace>\n'
        f'\t<ColorManagementSettings>{{"graphicsWhiteLuminance":203,"lutInterpolationMethod":1}}</ColorManagementSettings>\n'
        f'</VideoTrackGroup>'
    )


# T_AUDIOTRACKS 内 4 条 AudioClipTrack 的固定 UID（顺序=Index 0..3）
AUDIO_TRACK_UID = (
    "9f8d4cf9-00f4-4244-8ae8-4cfad6d74522",
    "645c2ec8-66c5-4a9c-bf0f-0498f012b008",
    "a55bc22c-a7a6-4398-a94c-0a27c7a19047",
    "e982ee18-af6a-4247-aa1d-8bfcb3e80966",
)


def x_audio_track_group():
    """AudioTrackGroup#101：引用 4 条音频轨道 UID（示例原文）。"""
    tracks = "\n".join(
        f'\t\t\t\t<Track Index="{i}" ObjectURef="{u}"/>'
        for i, u in enumerate(AUDIO_TRACK_UID)
    )
    return (
        f'<AudioTrackGroup ObjectID="101" ClassID="9b9238b9-53a8-4cc3-b03f-b36246d052e6" Version="6">\n'
        f'\t<TrackGroup Version="1">\n'
        f'\t\t<Tracks Version="1">\n'
        f'{tracks}\n'
        f'\t\t</Tracks>\n'
        f'\t\t<FrameRate>5760000</FrameRate>\n'
        f'\t\t<NextTrackID>6</NextTrackID>\n'
        f'\t</TrackGroup>\n'
        f'\t<MasterTrack ObjectRef="103"/>\n'
        f'\t<AutomationSafeFlags>0</AutomationSafeFlags>\n'
        f'\t<ID>1b9d0d22-db64-42e4-ab7a-d07119458628</ID>\n'
        f'\t<NumAdaptiveChannels>2</NumAdaptiveChannels>\n'
        f'</AudioTrackGroup>'
    )


def x_data_track_group():
    """DataTrackGroup#102（示例原文）。"""
    return (
        f'<DataTrackGroup ObjectID="102" ClassID="b714b71d-6838-48dd-9b77-db19088ced7e" Version="1">\n'
        f'\t<TrackGroup Version="1">\n'
        f'\t\t<FrameRate>10160640000</FrameRate>\n'
        f'\t\t<NextTrackID>1</NextTrackID>\n'
        f'\t</TrackGroup>\n'
        f'</DataTrackGroup>'
    )


def x_video_clip_track(track_guid, index, track_id, srcnum, srcstate,
                       targeted, item_ids, trans_ids):
    items = "\n".join(
        f'\t\t\t\t\t<TrackItem Index="{i}" ObjectRef="{oid}"/>'
        for i, oid in enumerate(item_ids)
    )
    trans = "\n".join(
        f'\t\t\t\t\t<TrackItem Index="{i}" ObjectRef="{oid}"/>'
        for i, oid in enumerate(trans_ids)
    )
    tgt = f'\t\t\t\t\t<MZ.TrackTargeted>{targeted}</MZ.TrackTargeted>\n' if targeted is not None else ""
    return (
        f'<VideoClipTrack ObjectUID="{track_guid}" ClassID="f68dcd81-8805-11d5-af2d-9bfa89d4ddd4" Version="1">\n'
        f'\t<ClipTrack Version="2">\n'
        f'\t\t<Track Version="3">\n'
        f'\t\t\t<Node Version="1">\n'
        f'\t\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t\t<MZ.SourceTrackNumber>{srcnum}</MZ.SourceTrackNumber>\n'
        f'\t\t\t\t\t<MZ.SourceTrackState>{srcstate}</MZ.SourceTrackState>\n'
        f'{tgt}'
        f'\t\t\t\t\t<TL.SQTrackExpanded>0</TL.SQTrackExpanded>\n'
        f'\t\t\t\t\t<TL.SQTrackExpandedHeight>25</TL.SQTrackExpandedHeight>\n'
        f'\t\t\t\t\t<TL.SQTrackShy>0</TL.SQTrackShy>\n'
        f'\t\t\t\t</Properties>\n'
        f'\t\t\t</Node>\n'
        f'\t\t\t<MediaType>228cda18-3625-4d2d-951e-348879e4ed93</MediaType>\n'
        f'\t\t\t<Index>{index}</Index>\n'
        f'\t\t\t<ID>{track_id}</ID>\n'
        f'\t\t\t<IsLocked>false</IsLocked>\n'
        f'\t\t\t<IsSyncLocked>true</IsSyncLocked>\n'
        f'\t\t\t<IsMuted>false</IsMuted>\n'
        f'\t\t</Track>\n'
        f'\t\t<ClipItems Version="3">\n'
        f'\t\t\t<TrackItems Version="1">\n'
        f'{items}\n'
        f'\t\t\t</TrackItems>\n'
        f'\t\t\t<MediaType>228cda18-3625-4d2d-951e-348879e4ed93</MediaType>\n'
        f'\t\t\t<Index>{index}</Index>\n'
        f'\t\t</ClipItems>\n'
        f'\t\t<TransitionItems Version="3">\n'
        f'\t\t\t<TrackItems Version="1">\n'
        f'{trans}\n'
        f'\t\t\t</TrackItems>\n'
        f'\t\t\t<MediaType>228cda18-3625-4d2d-951e-348879e4ed93</MediaType>\n'
        f'\t\t\t<Index>{index}</Index>\n'
        f'\t\t</TransitionItems>\n'
        f'\t</ClipTrack>\n'
        f'</VideoClipTrack>'
    )


def x_video_clip_track_item(item_id, start, end, chain_id, subclip_id,
                            w, h, head_trans=None, tail_trans=None):
    extra = ""
    if head_trans is not None:
        extra += f'\n\t\t<HeadTransition ObjectRef="{head_trans}"/>'
    if tail_trans is not None:
        extra += f'\n\t\t<TailTransition ObjectRef="{tail_trans}"/>'
    return (
        f'<VideoClipTrackItem ObjectID="{item_id}" ClassID="368b0406-29e3-4923-9fcd-094fbf9a1089" Version="6">\n'
        f'\t<ClipTrackItem Version="8">\n'
        f'\t\t<ComponentOwner Version="1">\n'
        f'\t\t\t<Components ObjectRef="{chain_id}"/>\n'
        f'\t\t</ComponentOwner>\n'
        f'\t\t<TrackItem Version="3">\n'
        f'\t\t\t<Start>{start}</Start>\n'
        f'\t\t\t<End>{end}</End>\n'
        f'\t\t</TrackItem>\n'
        f'\t\t<SubClip ObjectRef="{subclip_id}"/>{extra}\n'
        f'\t</ClipTrackItem>\n'
        f'\t<FrameRect>0,0,{w},{h}</FrameRect>\n'
        f'\t<PixelAspectRatio>1,1</PixelAspectRatio>\n'
        f'</VideoClipTrackItem>'
    )


def x_video_component_chain(comp_id, components, active=2):
    comps = "\n".join(
        f'\t\t<Component Index="{i}" ObjectRef="{cid}"/>'
        for i, cid in enumerate(components)
    )
    return (
        f'<VideoComponentChain ObjectID="{comp_id}" ClassID="0970e08a-f58f-4108-b29a-1a717b8e12e2" Version="3">\n'
        f'\t<ComponentChain Version="3">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<MZ.ComponentChain.ActiveComponentID>{active}</MZ.ComponentChain.ActiveComponentID>\n'
        f'\t\t\t\t<MZ.ComponentChain.ActiveComponentParamIndex>4294967295</MZ.ComponentChain.ActiveComponentParamIndex>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<Components Version="1">\n'
        f'{comps}\n'
        f'\t\t</Components>\n'
        f'\t</ComponentChain>\n'
        f'\t<DefaultOpacity>true</DefaultOpacity>\n'
        f'\t<DefaultOpacityComponentID>2</DefaultOpacityComponentID>\n'
        f'</VideoComponentChain>'
    )


def x_subclip(subclip_id, clip_id, master_guid, name):
    return (
        f'<SubClip ObjectID="{subclip_id}" ClassID="e0c58dc9-dbdd-4166-aef7-5db7e3f22e84" Version="5">\n'
        f'\t<Clip ObjectRef="{clip_id}"/>\n'
        f'\t<MasterClip ObjectURef="{master_guid}"/>\n'
        f'\t<Name>{escape(name)}</Name>\n'
        f'\t<OrigChGrp>0</OrigChGrp>\n'
        f'</SubClip>'
    )


def x_timeline_video_clip(alloc, clip_id, photo):
    return (
        f'<VideoClip ObjectID="{clip_id}" ClassID="9308dbef-2440-4acb-9ab2-953b9a4e82ec" Version="11">\n'
        f'\t<Clip Version="18">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<BE.Prefs.StillImages.DefaultIsDropFrame>false</BE.Prefs.StillImages.DefaultIsDropFrame>\n'
        f'\t\t\t\t<asl.clip.label.color>14910691</asl.clip.label.color>\n'
        f'\t\t\t\t<asl.clip.label.name>BE.Prefs.LabelColors.3</asl.clip.label.name>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t</Node>\n'
        f'\t\t<MarkerOwner Version="1">\n'
        f'\t\t\t<Markers ObjectRef="{photo.markers_id}"/>\n'
        f'\t\t</MarkerOwner>\n'
        f'\t\t<Source ObjectRef="{photo.source_id}"/>\n'
        f'\t\t<ClipID>{alloc.uid()}</ClipID>\n'
        f'\t\t<InPoint>0</InPoint>\n'
        f'\t\t<OutPoint>{photo.src_ticks}</OutPoint>\n'
        f'\t</Clip>\n'
        f'</VideoClip>'
    )


# ---------------------------------------------------------------------------
# 过渡效果
# ---------------------------------------------------------------------------
# 转场类型（MatchName 取证自 Premiere 2022 安装目录 Mezzanine.dll 的转场注册表；
# 无 AE. 前缀者为 Premiere 原生转场，工程内以"无 VideoFilterComponent"形式存储，
# 与示例中的"中心拆分"一致；带 AE. 前缀者需精确滤镜参数，仅保留已验证的两种）
TRANS_TYPES = {
    # —— 已验证（示例工程取证）——
    "cross":       dict(display="交叉溶解", match="AE.ADBE Cross Dissolve New", weight=20),
    "center":      dict(display="中心拆分", match="ADBE Center Split", weight=10),
    "iris":        dict(display="VR 光圈擦除", match="AE.Mettle SkyBox Iris Wipe", weight=8),
    # —— 溶解类（Mezzanine.dll 注册表）——
    "additive":    dict(display="叠加溶解", match="ADBE Additive Dissolve", weight=8),
    "dip_black":   dict(display="淡出黑场", match="ADBE Dip To Black", weight=8),
    "dip_white":   dict(display="淡出白场", match="ADBE Dip To White", weight=6),
    # —— 光圈类 ——
    "iris_round":  dict(display="圆形光圈", match="ADBE Iris Round", weight=6),
    "iris_cross":  dict(display="十字光圈", match="ADBE Iris Cross", weight=4),
    "iris_diamond": dict(display="菱形光圈", match="ADBE Iris Diamond", weight=4),
    "iris_points": dict(display="点状光圈", match="ADBE Iris Points", weight=4),
    "iris_square": dict(display="方形光圈", match="ADBE Iris Square", weight=4),
    "barn":        dict(display="门帘", match="ADBE Barn Doors", weight=3),
    # —— 擦除类 ——
    "clock":       dict(display="时钟擦除", match="ADBE Clock Wipe", weight=6),
    "radial":      dict(display="径向擦除", match="ADBE Radial Wipe", weight=5),
    "inset":       dict(display="插入擦除", match="ADBE Inset", weight=3),
    "split":       dict(display="分割", match="ADBE Split", weight=4),
    # —— 块状类 ——
    "zoom":        dict(display="缩放盒子", match="ADBE Zoom Boxes", weight=4),
    "random":      dict(display="随机块", match="ADBE Random Blocks", weight=5),
    "spiral":      dict(display="螺旋盒子", match="ADBE Spiral Boxes", weight=3),
    "zigzag":      dict(display="锯齿块", match="ADBE Zig-Zag Blocks", weight=3),
}


class Transition:
    def __init__(self, alloc, ttype, start, end, align):
        self.id = alloc.oid()
        self.start = start
        self.end = end
        self.align = align
        self.display = TRANS_TYPES[ttype]["display"]
        self.match = TRANS_TYPES[ttype]["match"]
        self.filter_xml = ""
        self.filter_id = None
        if ttype == "cross":
            self.filter_id = alloc.oid()
            p = param_video(alloc, "Input", 1, 13, "4294967293,0,0,0,0,0,0",
                            "0", "4294967295",
                            dclass="2f2eb0a3-318c-4a93-99fc-f1d319edc864")
            self.filter_xml = (filter_component(alloc, self.filter_id, [p], 0,
                                                "交叉溶解", "false",
                                                "AE.ADBE Cross Dissolve New")
                               + "\n" + p)
        elif ttype == "iris":
            self.filter_id = alloc.oid()
            params = [
                param_video(alloc, "输入", 1, 13, "4294967293,0,0,0,0,0,0",
                            "0", "4294967295",
                            dclass="2f2eb0a3-318c-4a93-99fc-f1d319edc864"),
                param_video(alloc, "过渡完成", 2, 2, "0.,0,0,0,0,0,0", "0", "100"),
                param_video(alloc, "自动 VR 属性", 6, 4, "true,0,0,0,0,0,0",
                            "false", "true",
                            dclass="cc12343e-f113-4d3b-ae05-b287db77d461",
                            discontinuous=True),
                param_video(alloc, "帧布局", 5, 7, "0,0,0,0,0,0,0", "0", "2",
                            dclass="6e02e8bb-2569-46b2-8ab1-4ab11c43e9c8",
                            discontinuous=True),
                param_video(alloc, "水平视角", 7, 8, "360.,0,0,0,0,0,0", "60", "360",
                            dclass="a4ff2d6e-7ac2-44f8-9d52-17d9ca50e542"),
                param_video(alloc, "垂直视角", 8, 8, "180.,0,0,0,0,0,0", "60", "180",
                            dclass="a4ff2d6e-7ac2-44f8-9d52-17d9ca50e542"),
                param_point(alloc, "目标点", 3),
                param_video(alloc, "羽化", 4, 8, "0.100000001490116119384766,0,0,0,0,0,0",
                            "0", "1", dclass="a4ff2d6e-7ac2-44f8-9d52-17d9ca50e542"),
            ]
            self.filter_xml = (filter_component(alloc, self.filter_id, params, 0,
                                                "VR 光圈擦除", "false",
                                                "AE.Mettle SkyBox Iris Wipe",
                                                (IRIS_BODY, IRIS_HASH))
                               + "\n" + "\n".join(params))


def x_video_transition(trans):
    body = [
        f'<VideoTransitionTrackItem ObjectID="{trans.id}" ClassID="3eeaed31-f78e-4144-b8e8-077656517181" Version="5">',
        '\t<TransitionTrackItem Version="3">',
        '\t\t<TrackItem Version="3">',
        f'\t\t\t<Start>{trans.start}</Start>',
        f'\t\t\t<End>{trans.end}</End>',
        '\t\t</TrackItem>',
        f'\t\t<Alignment>{trans.align}</Alignment>',
        f'\t\t<DisplayName>{escape(trans.display)}</DisplayName>',
        f'\t\t<MatchName>{trans.match}</MatchName>',
        '\t\t<HasOutgoingClip>true</HasOutgoingClip>',
        '\t\t<HasIncomingClip>true</HasIncomingClip>',
        '\t</TransitionTrackItem>',
    ]
    if trans.filter_id is not None:
        body.append(f'\t<VideoFilterComponent ObjectRef="{trans.filter_id}"/>')
    body += [
        '\t<StartPosition>0.5,0.5</StartPosition>',
        '\t<EndPosition>0.5,0.5</EndPosition>',
        '\t<StartPercent>0</StartPercent>',
        '\t<CenterPosition>0.5,0.5</CenterPosition>',
        '\t<EndPercent>1</EndPercent>',
        '\t<BorderWidth>0</BorderWidth>',
        '\t<BorderColor>0,0,0</BorderColor>',
        '\t<SwitchSources>false</SwitchSources>',
        '\t<Reverse>false</Reverse>',
        '\t<Direction>0</Direction>',
        '\t<AntiAliasQuality>1</AntiAliasQuality>',
        '</VideoTransitionTrackItem>',
    ]
    return "\n".join(body)


# ---------------------------------------------------------------------------
# 照片 / 序列对象（UID 在创建时分配；编号 ID 在发射阶段按文件顺序分配）
# ---------------------------------------------------------------------------
class Photo:
    def __init__(self, name, path, w, h, src_ticks):
        self.name = name
        self.path = path
        self.w = w
        self.h = h
        self.src_ticks = src_ticks
        self.clip_guid = str(uuid.uuid4())
        self.master_guid = str(uuid.uuid4())
        self.media_guid = str(uuid.uuid4())
        self.meta_guid = str(uuid.uuid4())
        # 编号 ID —— 由 assign_* 在发射顺序中分配
        self.logging_id = None
        self.bin_clip_id = None
        self.channel_group_id = None
        self.markers_id = None
        self.source_id = None
        self.stream_id = None
        self.bg_item_id = None
        self.fg_item_id = None
        self.bg_subclip_id = None
        self.fg_subclip_id = None
        self.bg_clip_id = None
        self.fg_clip_id = None
        self.bg_chain_id = None
        self.fg_chain_id = None
        self.bg_motion_id = None
        self.bg_blur_id = None
        self.fg_motion_id = None


class Sequence:
    def __init__(self, name, total):
        self.name = name
        self.total = total
        self.clip_guid = str(uuid.uuid4())
        self.master_guid = str(uuid.uuid4())
        self.sequence_guid = str(uuid.uuid4())
        self.logging_id = None
        self.audio_chain_id = None
        self.bin_clip_ids = [None, None]
        self.channel_group_id = None
        self.audio_source_id = None
        self.video_source_id = None
        self.sec1_id = None
        self.sec2_id = None
        self.channel_vec_id = None
        self.ch0_id = None
        self.ch1_id = None


# ---------------------------------------------------------------------------
# 运动规划
# ---------------------------------------------------------------------------
def plan_motion(photo, seq_w, seq_h, args, rng):
    """返回前景层运动规划 (v0, v1, pan)。

    v0/v1：缩放关键帧（%）；pan：位置锚点关键帧 (px0,py0,px1,py1)，
    无平移时 pan=None（锚点恒为画面中心 0.5,0.5）。
    运动种类：纯缩放（放大/缩小）、单向平移（左/右/上/下）、缩放+平移组合。
    横图满屏铺满：平移余量由缩放提供（用掉余量的 40%~75%，总移动约 3%~8% 画面）；
    竖图高度铺满、宽度不足：平移时露出下层模糊背景，横向取画面宽度的 2%~4%、
    纵向取 1.5%~3%（轻微，避免幅度过大破坏画面稳定感）。
    """
    w, h = photo.w, photo.h
    landscape = w >= h
    if landscape:
        base = max(seq_w / w, seq_h / h) * 100.0      # 横图满屏铺满
    else:
        base = seq_h / h * 100.0                       # 竖图高度铺满

    kind = rng.choices(
        ["zoom_in", "zoom_out", "pan_l", "pan_r", "pan_u", "pan_d", "zoom_pan"],
        weights=[20, 15, 14, 14, 7, 7, 23])[0]

    if kind.startswith("pan"):
        # 平移需要更大的缩放余量来提供移动空间（6%~10%）
        delta = rng.uniform(max(args.zoom_min, 6.0), min(args.zoom_max + 4.0, 10.0))
    else:
        delta = rng.uniform(args.zoom_min, args.zoom_max)
    v0 = base
    v1 = min(base + delta, args.max_scale)

    pan = None
    if kind == "zoom_pan" and rng.random() < 0.5:
        v0, v1 = v1, base                     # 组合：缩小 + 平移
    elif kind == "zoom_out":
        v0, v1 = v1, base                     # 纯缩小

    if kind.startswith("pan") or kind == "zoom_pan":
        if landscape:
            slack = (v1 / base - 1) / 2       # 每侧平移余量（缩放提供）
            if slack > 0.003:
                m = rng.uniform(0.4, 0.75) * slack
                if kind in ("pan_u", "pan_d"):
                    dx, dy = 0.0, m if kind == "pan_u" else -m
                else:
                    dx = m if (kind == "pan_l"
                               or (kind == "zoom_pan" and rng.random() < 0.5)) else -m
                    dy = 0.0
                pan = (0.5 - dx, 0.5 - dy, 0.5 + dx, 0.5 + dy)
        else:
            if kind in ("pan_u", "pan_d"):
                dy = rng.uniform(0.015, 0.03) * (1 if kind == "pan_u" else -1)
                pan = (0.5, 0.5 - dy, 0.5, 0.5 + dy)
            else:
                dx = rng.uniform(0.02, 0.04) * (1 if (kind == "pan_l"
                                                      or (kind == "zoom_pan" and rng.random() < 0.5)) else -1)
                pan = (0.5 - dx, 0.5, 0.5 + dx, 0.5)
    return v0, v1, pan


# ---------------------------------------------------------------------------
# 验证
# ---------------------------------------------------------------------------
def validate(doc):
    """解析自身输出并检查引用完整性（生成工具的自我验证）。"""
    root = ET.fromstring(doc)
    seen_oid = {}          # 唯一性检查：只查生成器自分配段
    all_oids = set()       # 引用解析：全部 ObjectID
    seen_uid = {}
    for el in root.iter():
        oid = el.attrib.get("ObjectID")
        if oid is not None:
            all_oids.add(oid)
            # 模板/视图状态与真实对象天然共用小 ID(1~178)，只校验生成器自分配段(>=1000)
            if oid.isdigit() and int(oid) >= 1000:
                if oid in seen_oid:
                    raise RuntimeError(f"重复的 ObjectID: {oid}")
                seen_oid[oid] = el.tag
        uid = el.attrib.get("ObjectUID")
        if uid is not None:
            if uid in seen_uid:
                raise RuntimeError(f"重复的 ObjectUID: {uid}")
            seen_uid[uid] = el.tag
    missing_refs = []
    for el in root.iter():
        for attr in ("ObjectRef", "ObjectURef"):
            ref = el.attrib.get(attr)
            if ref is None:
                continue
            if attr == "ObjectRef" and ref not in all_oids:
                missing_refs.append((el.tag, attr, ref))
            if attr == "ObjectURef" and ref not in seen_uid:
                missing_refs.append((el.tag, attr, ref))
    if missing_refs:
        raise RuntimeError(f"未解析的引用({len(missing_refs)}): " + repr(missing_refs[:8]))
    return len(seen_oid), len(seen_uid)


# ---------------------------------------------------------------------------
# 主流程
# ---------------------------------------------------------------------------
def build(args, out_path, pic_dir, rng):
    alloc = Alloc(1000)
    proj_dir = os.path.dirname(out_path)

    exts = {".jpg", ".jpeg", ".png", ".bmp", ".gif", ".tif", ".tiff", ".webp"}
    files = [fn for fn in os.listdir(pic_dir)
             if os.path.splitext(fn)[1].lower() in exts]
    # 照片顺序：随机(默认) / 文件名升/降序 / 创建时间升/降序
    order = (args.order or "random").lower()
    if order == "random":
        rng.shuffle(files)
    elif order == "name_asc":
        files.sort(key=natural_key)
    elif order == "name_desc":
        files.sort(key=natural_key, reverse=True)
    elif order == "ctime_asc":
        files.sort(key=lambda fn: os.path.getctime(os.path.join(pic_dir, fn)))
    elif order == "ctime_desc":
        files.sort(key=lambda fn: os.path.getctime(os.path.join(pic_dir, fn)),
                   reverse=True)
    else:
        raise SystemExit(f"未知的照片排序方式: {args.order}")
    if not files:
        raise SystemExit(f"目录中没有找到图片: {pic_dir}")
    if args.limit:
        files = files[:args.limit]

    photos = []
    for fn in files:
        path = os.path.join(pic_dir, fn)
        size = img_size(path)
        if size is None:
            size = (1920, 1440)
            print(f"  [warn] 无法读取尺寸，按 4:3 处理: {fn}")
        photos.append((fn, path, size[0], size[1]))
    n = len(photos)

    # 每张照片时长（随机 min~max 秒，按 30fps 取整到帧）
    dur_frames = []
    for _ in range(n):
        sec = rng.uniform(args.min_dur, args.max_dur)
        dur_frames.append(max(1, round(sec * 30)))
    starts = [0]
    for f in dur_frames[:-1]:
        starts.append(starts[-1] + f * SEQ_FRAME)
    ends = [starts[i] + f * SEQ_FRAME for i, f in enumerate(dur_frames)]
    total = ends[-1]

    t_before = (args.trans_frames // 2) * SEQ_FRAME
    t_after = (args.trans_frames - args.trans_frames // 2) * SEQ_FRAME
    align = t_before

    # ---------------- 背景音乐查找（可选） ----------------
    # 模式 A：--music 指定单文件（该文件循环铺满时间线）
    # 模式 B（默认）：收集音乐目录下全部曲目（Intro/Main 成对），依次播放，
    #              全部播完仍不够覆盖视频时从头循环
    _AUDIO_EXTS = {".aac", ".mp3", ".m4a", ".wav", ".wma", ".ogg", ".flac"}
    music_files = []          # list[(abspath, 显示名)]
    music_note = None
    if args.music:
        f = os.path.abspath(args.music)
        if not os.path.isfile(f):
            raise SystemExit(f"指定的背景音乐文件不存在: {args.music}")
        music_files.append((f, os.path.basename(f)))
        music_note = f"指定文件 {os.path.basename(f)}"
    else:
        audio_local = os.path.join(proj_dir, "Audio")
        src_dir = None
        if args.music_dir:
            src_dir = os.path.abspath(args.music_dir)
        elif os.path.isdir(audio_local):
            src_dir = audio_local
        else:
            mdir = os.path.join(os.environ.get("LOCALAPPDATA", ""),
                                "Packages",
                                "Microsoft.Windows.Photos_8wekyb3d8bbwe",
                                "LocalState", "Slideshow", "Music", "Audio")
            if os.path.isdir(mdir):
                src_dir = mdir
        if src_dir is not None:
            style = (args.music_style or "").lower()
            track = (args.music_track or "").lower()
            cands = [fn for fn in os.listdir(src_dir)
                     if os.path.splitext(fn)[1].lower() in _AUDIO_EXTS]
            cands = [fn for fn in cands
                     if (not style or style in fn.lower())
                     and (not track or f"_{track}." in fn.lower())]
            cands.sort(key=natural_key)
            if cands:
                # 模式 B：全部曲目（成对：Intro 在前、Main 在后）
                if src_dir is audio_local:
                    music_files = [(os.path.join(audio_local, fn), fn) for fn in cands]
                    music_note = f"工作目录 Audio\\ 全部 {len(cands)} 首"
                else:
                    os.makedirs(audio_local, exist_ok=True)
                    music_files = []
                    for fn in cands:
                        src_abs = os.path.abspath(os.path.join(src_dir, fn))
                        dst = os.path.join(audio_local, fn)
                        if os.path.abspath(dst) != src_abs:
                            shutil.copy2(src_abs, dst)
                        music_files.append((dst, fn))
                    music_note = f"照片应用音乐库全部 {len(cands)} 首（已复制到 Audio\\）"
    # 解析音频时长（仅 .aac 自动支持）并规划播放计划
    music = None
    if music_files:
        fade_ticks = max(1, round(args.fade_sec * 30)) * SEQ_FRAME
        fade_ticks = min(fade_ticks, max(total // 2, SEQ_FRAME))
        # 曲目配对：`*_Intro.aac` / `*_Main.aac` 按同名前缀成一首（Intro 先播）
        pairs = {}
        for f, fn in music_files:
            if fn.lower().endswith("_intro.aac"):
                prefix = fn[:-len("_intro.aac")]
                pairs.setdefault(prefix, {})["intro"] = f
            elif fn.lower().endswith("_main.aac"):
                prefix = fn[:-len("_main.aac")]
                pairs.setdefault(prefix, {})["main"] = f
            else:
                pairs.setdefault(fn, {})["solo"] = f
        tracks = []
        for prefix in sorted(pairs, key=natural_key):
            d = pairs[prefix]
            for part in ("intro", "main", "solo"):
                if part in d:
                    f, fn = d[part], f"{prefix}_{part}.aac" if part != "solo" else prefix
                    dur = aac_duration(f)
                    if dur is None or dur <= 0:
                        print(f"  [music] 跳过无法解析的音频: {fn}")
                        continue
                    tracks.append(AudioTrack(fn, f, dur))
        if not tracks:
            raise SystemExit("未找到可用的背景音乐（AAC 解析失败）")
        music = AudioMusic(tracks, fade_ticks)
        build_audio_plan(music, total)
        total_sec = sum(t.dur_sec for t in music.tracks)
        loops = music.n_seg / len(music.tracks) if music.tracks else 0
        print(f"  [music] 配乐 {len(music.tracks)} 段（{total_sec:.1f}s 总长），"
              f"按序播放共 {music.n_seg} 段填满 {total / SEQ_TB:.1f}s"
              + (f"（循环 {loops:.2f} 轮）" if loops > 1 else "") +
              f" | 结尾渐弱 {fade_ticks / SEQ_TB:.1f}s ({music_note})")

    kinds = list(TRANS_TYPES.keys())
    weights = [TRANS_TYPES[k]["weight"] for k in kinds]
    trans_kinds = [rng.choices(kinds, weights=weights)[0] for _ in range(max(0, n - 1))]

    photos_obj = []
    for fn, path, w, h in photos:
        src_ticks = max(1, round(dur_frames[len(photos_obj)] / 30 * 25)) * SRC_FRAME
        photos_obj.append(Photo(fn, path, w, h, src_ticks))
    seq = Sequence(args.seq_name, total)
    track_bg_guid = str(uuid.uuid4())
    track_fg_guid = str(uuid.uuid4())
    track_v3_guid = str(uuid.uuid4())
    track_v4_guid = str(uuid.uuid4())

    # ---------------- 编号 ID 按发射顺序分配（保证文件内升序） ----------------
    # A. 照片素材库三元组：LoggingInfo / bin VideoClip / ChannelGroup
    for p in photos_obj:
        p.logging_id = alloc.oid()
        p.bin_clip_id = alloc.oid()
        p.channel_group_id = alloc.oid()
    # C. 序列素材库：LoggingInfo / AudioComponentChain / AudioClip / VideoClip / ChannelGroup
    seq.logging_id = alloc.oid()
    seq.audio_chain_id = alloc.oid()
    seq.bin_clip_ids[0] = alloc.oid()
    seq.bin_clip_ids[1] = alloc.oid()
    seq.channel_group_id = alloc.oid()
    # B. 照片 Markers / VideoMediaSource
    for p in photos_obj:
        p.markers_id = alloc.oid()
        p.source_id = alloc.oid()
    # D. 序列源：AudioSequenceSource / SecondaryContent×2 / VideoSequenceSource /
    #    ClipChannelVectorSerializer / ClipChannelSerializer×2
    seq.audio_source_id = alloc.oid()
    seq.sec1_id = alloc.oid()
    seq.sec2_id = alloc.oid()
    seq.video_source_id = alloc.oid()
    seq.channel_vec_id = alloc.oid()
    seq.ch0_id = alloc.oid()
    seq.ch1_id = alloc.oid()
    # E. 照片 VideoStream（与 Media 同组）
    for p in photos_obj:
        p.stream_id = alloc.oid()
    # F. 时间线条目（先全部背景、再全部前景，与发射顺序一致）
    for p in photos_obj:
        p.bg_item_id = alloc.oid()
    for p in photos_obj:
        p.fg_item_id = alloc.oid()
    # G. 转场对象（仅前景轨 V2；滤镜与参数 ID 在构造时分配）
    fg_trans = []
    for i in range(n - 1):
        s = starts[i + 1] - t_before
        e = starts[i + 1] + t_after
        fg_trans.append(Transition(alloc, trans_kinds[i], s, e, align))
    # H. 组件链 + SubClip
    for p in photos_obj:
        p.bg_chain_id = alloc.oid()
        p.bg_subclip_id = alloc.oid()
        p.fg_chain_id = alloc.oid()
        p.fg_subclip_id = alloc.oid()
    # I. 时间线实例 Clip
    for p in photos_obj:
        p.bg_clip_id = alloc.oid()
        p.fg_clip_id = alloc.oid()
    # J. 滤镜 ID（运动/模糊各照片一组；参数在发射阶段分配）
    for p in photos_obj:
        p.bg_motion_id = alloc.oid()
        p.bg_blur_id = alloc.oid()
        p.fg_motion_id = alloc.oid()

    # ---------------- 组装（发射顺序 == 编号分配顺序） ----------------
    L = []
    L.append('<?xml version="1.0" encoding="UTF-8" ?>')
    L.append('<PremiereData Version="3">')
    L.append('\t<Project ObjectRef="1"/>')
    L.append('\t<Project ObjectID="1" ClassID="62ad66dd-0dcd-42da-a660-6d8fbde94876" Version="40">')

    # 项目视图状态（模板 + 补丁）
    view = T_VIEWSTATE
    view = view.replace("493da62d-1e78-44c8-9a93-e7a5bbcaee4f", seq.sequence_guid)
    view = view.replace("b057b38d-9f44-4ef9-be11-4b77ff681e1e", str(uuid.uuid4()))
    view = view.replace(r"C:\workspace\20261011照片转幻灯片放映视频\example\未命名.prproj",
                        "\\\\?\\" + out_path)
    L.append(view)

    root_guid = str(uuid.uuid4())
    L.append(f'\t<RootProjectItem ObjectURef="{root_guid}"/>')
    for ref, name in ((3, "ProjectSettings"), (4, "MovieCompileSettings"),
                      (5, "StillCompileSettings"), (6, "AudioCompileSettings"),
                      (7, "CustomCompileSettings"), (8, "VideoPreviewCompileSettings"),
                      (9, "ScratchDiskSettings"), (10, "IngestSettings"),
                      (11, "ProjectWorkspace")):
        L.append(f'\t<{name} ObjectRef="{ref}"/>')
    L.append('\t<NextSequenceID>2</NextSequenceID>')
    L.append('\t<NextID>1000001</NextID>')
    L.append('\t</Project>')

    # RootProjectItem 定义
    items = "\n".join(
        f'\t\t\t\t<Item Index="{i}" ObjectURef="{obj.clip_guid}"/>'
        for i, obj in enumerate(photos_obj)
    )
    items += f'\n\t\t\t\t<Item Index="{n}" ObjectURef="{seq.clip_guid}"/>'
    if music is not None:
        for idx, t in enumerate(music.tracks):
            items += f'\n\t\t\t\t<Item Index="{n + 1 + idx}" ObjectURef="{t.clip_guid}"/>'
    L.append(
        f'<RootProjectItem ObjectUID="{root_guid}" ClassID="1c307a89-9318-47d7-a583-bf2553736543" Version="1">\n'
        f'\t<ProjectItem Version="1">\n'
        f'\t\t<Node Version="1">\n'
        f'\t\t\t<Properties Version="1">\n'
        f'\t\t\t\t<list.view.expanded.state.223c578b_45_01f9_45_4885_45_9d10_45_ac071ffaddc9>true</list.view.expanded.state.223c578b_45_01f9_45_4885_45_9d10_45_ac071ffaddc9>\n'
        f'\t\t\t</Properties>\n'
        f'\t\t\t<ID>1000000</ID>\n'
        f'\t\t</Node>\n'
        f'\t\t<Name>Root Bin</Name>\n'
        f'\t</ProjectItem>\n'
        f'\t<ProjectItemContainer Version="1">\n'
        f'\t\t<Items Version="1">\n'
        f'{items}\n'
        f'\t\t</Items>\n'
        f'\t</ProjectItemContainer>\n'
        f'</RootProjectItem>'
    )

    L.append(T_SETTINGS)
    misc1, misc2 = x_misc_settings()
    L.append(misc1)

    # 素材库 ClipProjectItem / MasterClip（UID）
    for i, p in enumerate(photos_obj):
        L.append(x_clip_project_item(p, grid_order=n - 1 - i))
    L.append(x_clip_project_item(seq, is_seq=True, grid_order=n))
    for p in photos_obj:
        L.append(x_master_clip(p, [p.bin_clip_id]))
    L.append(x_master_clip(seq, seq.bin_clip_ids, is_seq=True))
    L.append(misc2)

    # A. 照片素材库三元组
    for p in photos_obj:
        L.append(x_clip_logging(p))
        L.append(x_bin_video_clip(alloc, p))
        L.append(x_channel_group(p))
    # C. 序列素材库
    L.append(x_seq_logging(seq))
    L.append(x_seq_audio_chain(seq))
    L.append(x_seq_audio_clip(alloc, seq))
    L.append(x_seq_video_clip(alloc, seq))
    L.append(x_seq_channel_group(seq))
    # B. 照片 Markers / VideoMediaSource
    for p in photos_obj:
        L.append(x_markers(p))
        L.append(x_media_source(p))
    # D. 序列源（第一部分）
    L.append(x_seq_audio_source(seq))
    L.append(x_seq_sec_content(seq, seq.sec1_id, 0))
    L.append(x_seq_sec_content(seq, seq.sec2_id, 1))
    L.append(x_seq_video_source(seq))
    L.append(x_seq_channel_vec(seq))
    # Media（UID）
    for p in photos_obj:
        try:
            rel = os.path.relpath(p.path, proj_dir).replace("/", "\\")
        except ValueError:
            # 跨盘符无法相对化（照片在 G:\、工程在 C:\ 等），改用绝对路径
            rel = p.path.replace("/", "\\")
        L.append(x_media(alloc, p, rel, p.path))
    # 序列（UID）
    L.append(x_sequence(seq, total, track_bg_guid, track_fg_guid))
    # D. 序列源（第二部分：ClipChannelSerializer×2）
    L.append(x_seq_channel_serializer(seq, seq.ch0_id, 0))
    L.append(x_seq_channel_serializer(seq, seq.ch1_id, 1))

    # 轨道组：VideoTrackGroup#100 → AudioTrackGroup#101 → DataTrackGroup#102
    L.append(x_video_track_group(args.width, args.height,
                                 [track_bg_guid, track_fg_guid,
                                  track_v3_guid, track_v4_guid]))
    L.append(x_audio_track_group())
    L.append(x_data_track_group())
    # 视频轨道 ×4（V1 背景 / V2 前景 / V3、V4 空轨；TrackID 与示例一致 4,1,2,3）
    L.append(x_video_clip_track(track_bg_guid, 0, 4, -1, 0, None,
                                [p.bg_item_id for p in photos_obj], []))
    L.append(x_video_clip_track(track_fg_guid, 1, 1, 0, 2, 0,
                                [p.fg_item_id for p in photos_obj],
                                [t.id for t in fg_trans]))
    L.append(x_video_clip_track(track_v3_guid, 2, 2, -1, 0, 1, [], []))
    L.append(x_video_clip_track(track_v4_guid, 3, 3, -1, 0, 0, [], []))
    # 音频轨道：无音乐时直接发射空轨模板；有音乐时轨道发射挪到 K 段之后
    # （K 段 ID 在 J 段后分配，轨道无 ObjectID、前向引用安全）
    if music is None:
        L.append(T_AUDIOTRACKS)
    L.append(T_AUDIOCOMPS)
    L.append(T_AUDIOFADERS)
    L.append(T_AUDIOPARAMS)

    # E. 照片 VideoStream（动态段起点）
    for p in photos_obj:
        L.append(x_video_stream(p))

    # F. 时间线条目（背景无转场、前景挂转场，与示例一致）
    for i, p in enumerate(photos_obj):
        L.append(x_video_clip_track_item(p.bg_item_id, starts[i], ends[i],
                                         p.bg_chain_id, p.bg_subclip_id,
                                         args.width, args.height))
    for i, p in enumerate(photos_obj):
        h = fg_trans[i - 1].id if i > 0 else None
        t = fg_trans[i].id if i < n - 1 else None
        L.append(x_video_clip_track_item(p.fg_item_id, starts[i], ends[i],
                                         p.fg_chain_id, p.fg_subclip_id,
                                         args.width, args.height, h, t))
    # G. 转场对象（前景轨 V2 逐边界发射）
    for tr in fg_trans:
        L.append(x_video_transition(tr))
        if tr.filter_xml:
            L.append(tr.filter_xml)

    # H. 组件链 + SubClip（每张照片 bg、fg）
    for p in photos_obj:
        L.append(x_video_component_chain(p.bg_chain_id, [p.bg_motion_id, p.bg_blur_id]))
        L.append(x_subclip(p.bg_subclip_id, p.bg_clip_id, p.master_guid, p.name))
        L.append(x_video_component_chain(p.fg_chain_id, [p.fg_motion_id]))
        L.append(x_subclip(p.fg_subclip_id, p.fg_clip_id, p.master_guid, p.name))

    # I. 时间线实例 Clip
    for p in photos_obj:
        L.append(x_timeline_video_clip(alloc, p.bg_clip_id, p))
        L.append(x_timeline_video_clip(alloc, p.fg_clip_id, p))

    # J. 滤镜与参数（ID 已分配，此处只生成参数并发射）
    for p in photos_obj:
        # 背景：静态运动（宽度铺满缩放）+ 高斯模糊
        bg_width_fit = args.width / p.w * 100.0
        params = [
            param_point(alloc, "位置", 1),
            param_video(alloc, "缩放", 2, 2, f"{fmt_num(bg_width_fit)},0,0,0,0,0,0",
                        "0", "10000", upper_ui="200", cur=fmt_num(bg_width_fit)),
            param_video(alloc, "缩放宽度", 3, 2, "100.,0,0,0,0,0,0", "0", "10000", upper_ui="200"),
            param_video(alloc, " ", 4, 4, "true,0,0,0,0,0,0", "false", "true",
                        dclass="cc12343e-f113-4d3b-ae05-b287db77d461"),
            param_video(alloc, "旋转", 5, 3, "0.,0,0,0,0,0,0", "-32768", "32767"),
            param_point(alloc, "锚点", 6),
            param_video(alloc, "防闪烁滤镜", 7, 8, "0.,0,0,0,0,0,0", "0", "1",
                        dclass="a4ff2d6e-7ac2-44f8-9d52-17d9ca50e542"),
        ]
        L.append(filter_component(alloc, p.bg_motion_id, params, 1, "运动",
                                  "true", "AE.ADBE Motion", ("AQA=", MOTION_HASH)))
        L.append("\n".join(params))

        blur_params = [
            param_video(alloc, "模糊度", 1, 8, f"{fmt_num(args.blur)},0,0,0,0,0,0",
                        "0", "30000", upper_ui="50", cur=fmt_num(args.blur),
                        dclass="a4ff2d6e-7ac2-44f8-9d52-17d9ca50e542"),
            param_video(alloc, "模糊尺寸", 2, 7, "0,0,0,0,0,0,0", "0", "2",
                        dclass="6e02e8bb-2569-46b2-8ab1-4ab11c43e9c8", discontinuous=True),
            param_video(alloc, " ", 3, 4, "true,0,0,0,0,0,0", "false", "true",
                        dclass="cc12343e-f113-4d3b-ae05-b287db77d461"),
        ]
        L.append(filter_component(alloc, p.bg_blur_id, blur_params, 3, "高斯模糊",
                                  "false", "AE.ADBE Gaussian Blur 2"))
        L.append("\n".join(blur_params))

        # 前景：随机 Ken Burns 运动（缩放/平移/组合）
        v0, v1, pan = plan_motion(p, args.width, args.height, args, rng)
        dur_sec = dur_frames[photos_obj.index(p)] / 30.0
        kf1 = max(p.src_ticks - SRC_FRAME, 0)
        if kf1 <= 0:
            kf1 = p.src_ticks
        slope = (v1 - v0) / dur_sec
        params = []
        if pan is not None:
            px0, py0, px1, py1 = pan
            params.append(param_pos_keyframed(alloc, 0, kf1, px0, py0, px1, py1,
                                              (px1 - px0) / dur_sec))
            params.append(param_scale_keyframed(alloc, 0, kf1, v0, v1, slope, v1))
        else:
            params.append(param_point(alloc, "位置", 1))
            params.append(param_scale_keyframed(alloc, 0, kf1, v0, v1, slope, v1))
        params += [
            param_video(alloc, "缩放宽度", 3, 2, "100.,0,0,0,0,0,0", "0", "10000", upper_ui="200"),
            param_video(alloc, " ", 4, 4, "true,0,0,0,0,0,0", "false", "true",
                        dclass="cc12343e-f113-4d3b-ae05-b287db77d461"),
            param_video(alloc, "旋转", 5, 3, "0.,0,0,0,0,0,0", "-32768", "32767"),
            param_point(alloc, "锚点", 6),
            param_video(alloc, "防闪烁滤镜", 7, 8, "0.,0,0,0,0,0,0", "0", "1",
                        dclass="a4ff2d6e-7ac2-44f8-9d52-17d9ca50e542"),
        ]
        L.append(filter_component(alloc, p.fg_motion_id, params, 1, "运动",
                                  "true", "AE.ADBE Motion", ("AQA=", MOTION_HASH)))
        L.append("\n".join(params))

    # K. 背景音乐对象（每首曲目一套素材库 → 该曲目各播放段 → 渐弱滤镜 → 音频轨）
    if music is not None:
        mu = music
        # 编号 ID 在发射前分配（紧跟 J 段参数之后，保证文件内升序）
        for t in mu.tracks:
            t.logging_id = alloc.oid()
            t.bin_chain_id = alloc.oid()
            t.bin_clip_id = alloc.oid()
            t.channel_group_id = alloc.oid()
            t.markers_id = alloc.oid()
            t.source_id = alloc.oid()
            t.sec1_id = alloc.oid()
            t.sec2_id = alloc.oid()
            t.channel_vec_id = alloc.oid()
            t.ch0_id = alloc.oid()
            t.ch1_id = alloc.oid()
            t.stream_id = alloc.oid()
            for j in range(len(t.seg_starts)):
                t.seg_item_id[j] = alloc.oid()
            for j in range(len(t.seg_starts)):
                t.seg_chain_id[j] = alloc.oid()
            for j in range(len(t.seg_starts)):
                t.seg_subclip_id[j] = alloc.oid()
            for j in range(len(t.seg_starts)):
                t.seg_clip_id[j] = alloc.oid()
        mu.vol_filter_id = alloc.oid()
        mu.vol_bypass_id = alloc.oid()
        mu.vol_level_id = alloc.oid()
        mu.ch_filter_id = alloc.oid()
        mu.ch_bypass_id = alloc.oid()
        mu.ch_left_id = alloc.oid()
        mu.ch_right_id = alloc.oid()
        for i in range(30):
            mu.ch_zero_ids[i] = alloc.oid()

        # 发射：每首曲目素材库 + 该曲目全部播放段
        for t in mu.tracks:
            L.append(x_audio_logging(t))
            L.append(x_audio_bin_chain(t))
            L.append(x_audio_bin_clip(alloc, t))
            L.append(x_audio_channel_group(t))
            L.append(x_audio_markers(t))
            L.append(x_audio_media_source(t))
            L.append(x_audio_sec_content(t, t.sec1_id, 0))
            L.append(x_audio_sec_content(t, t.sec2_id, 1))
            L.append(x_audio_channel_vec(t))
            L.append(x_audio_channel_item(t, t.ch0_id, 0))
            L.append(x_audio_channel_item(t, t.ch1_id, 1))
            L.append(x_audio_stream(t))
            try:
                rel = os.path.relpath(t.path, proj_dir).replace("/", "\\")
            except ValueError:
                # 跨盘符无法相对化（音乐在 G:\、工程在 C:\ 等），改用绝对路径
                rel = t.path.replace("/", "\\")
            L.append(x_audio_media(alloc, t, rel, t.path))
            L.append(x_audio_clip_project_item(t))
            L.append(x_audio_master_clip(t))
            for j in range(len(t.seg_starts)):
                is_last = (t is mu.last_track and j == mu.last_seg_idx)
                L.append(x_audio_clip_track_item(alloc, t, j))
                L.append(x_audio_seg_chain(t, j, is_last,
                                           mu.vol_filter_id, mu.ch_filter_id))
                L.append(x_audio_subclip(t, j))
                in_pt = 0
                out_pt = t.seg_ends[j] - t.seg_starts[j]
                L.append(x_audio_clip(alloc, t, j, in_pt, out_pt))
        # 最后一段：音量（含结尾渐弱关键帧）+ 通道音量滤镜
        last_t = mu.last_track
        last_dur = last_t.seg_ends[mu.last_seg_idx] - last_t.seg_starts[mu.last_seg_idx]
        vol_params = [param_audio_bypass(alloc, mu.vol_bypass_id),
                      param_audio_level(alloc, mu.vol_level_id, last_dur, mu.fade_ticks)]
        L.append(audio_filter_component_audio(alloc, mu.vol_filter_id, vol_params,
                                              1, "音量", "Internal Volume Stereo"))
        L.append("\n".join(vol_params))
        ch_params = [param_audio_bypass(alloc, mu.ch_bypass_id),
                     param_audio_ch(alloc, mu.ch_left_id, "左侧"),
                     param_audio_ch(alloc, mu.ch_right_id, "右侧")]
        ch_params += [param_audio_zero(alloc, mu.ch_zero_ids[i]) for i in range(30)]
        L.append(audio_filter_component_audio(alloc, mu.ch_filter_id, ch_params,
                                              2, "通道音量", "Internal Channel Volume Stereo"))
        L.append("\n".join(ch_params))
        # 音频轨道（A1 挂载全部播放段，按时间线顺序；K 段 ID 已分配，前向引用成立）
        tracks_xml = T_AUDIOTRACKS
        items_xml = "\n".join(
            f'\t\t\t\t\t<TrackItem Index="{k}" ObjectRef="{mu.tracks[ti].seg_item_id[si]}"/>'
            for k, (ti, si) in enumerate(mu.seg_plan))
        old_ci = ('<ClipItems Version="3">\n'
                  '\t\t\t\t<MediaType>80b8e3d5-6dca-4195-aefb-cb5f407ab009</MediaType>\n'
                  '\t\t\t\t<Index>0</Index>\n'
                  '\t\t\t</ClipItems>')
        new_ci = ('<ClipItems Version="3">\n'
                  '\t\t\t\t<TrackItems Version="1">\n'
                  f'{items_xml}\n'
                  '\t\t\t\t</TrackItems>\n'
                  '\t\t\t\t<MediaType>80b8e3d5-6dca-4195-aefb-cb5f407ab009</MediaType>\n'
                  '\t\t\t\t<Index>0</Index>\n'
                  '\t\t\t</ClipItems>')
        if old_ci not in tracks_xml:
            raise RuntimeError("T_AUDIOTRACKS 首轨 ClipItems 结构未匹配，无法挂载音频片段")
        L.append(tracks_xml.replace(old_ci, new_ci, 1))

    L.append('</PremiereData>')

    doc = "\n".join(L)
    # 自我验证：XML 可解析 + 无重复 ID + 引用完整
    try:
        n_oid, n_uid = validate(doc)
    except Exception:
        dbg = os.path.join(proj_dir, "_调试输出.xml")
        with open(dbg, "w", encoding="utf-8") as f:
            f.write(doc)
        print(f"验证失败，已将 XML 转储到: {dbg}")
        raise
    with gzip.open(out_path, "wb") as f:
        f.write(doc.encode("utf-8"))
    return n, total, n_oid, n_uid, music


def main():
    ap = argparse.ArgumentParser(
        description="照片幻灯片 Premiere 工程生成器（生成 .prproj）")
    ap.add_argument("--pic-dir", default=None,
                    help="照片目录（默认: 本脚本所在目录的 PIC 子目录）")
    ap.add_argument("--out", default=None,
                    help="输出的 .prproj 路径（默认: 本脚本所在目录/照片幻灯片放映.prproj）")
    ap.add_argument("--width", type=int, default=3840, help="序列宽度（默认 3840，4K）")
    ap.add_argument("--height", type=int, default=2160, help="序列高度（默认 2160，4K）")
    ap.add_argument("--min-dur", type=float, default=3.0, help="每张照片最短时长（秒，默认 3）")
    ap.add_argument("--max-dur", type=float, default=5.0, help="每张照片最长时长（秒，默认 5）")
    ap.add_argument("--trans-frames", type=int, default=25,
                    help="转场时长（帧，默认 25，30fps 下约 0.83 秒）")
    ap.add_argument("--blur", type=float, default=300.0, help="背景高斯模糊值（默认 300）")
    ap.add_argument("--zoom-min", type=float, default=2.0, help="缩放幅度下限 %%（默认 2）")
    ap.add_argument("--zoom-max", type=float, default=6.0, help="缩放幅度上限 %%（默认 6）")
    ap.add_argument("--max-scale", type=float, default=110.0,
                    help="前景最大缩放 %%（默认 110）")
    ap.add_argument("--seq-name", default="照片幻灯片放映", help="序列名称")
    ap.add_argument("--seed", type=int, default=None, help="随机种子（不填则随机）")
    ap.add_argument("--limit", type=int, default=0, help="只使用前 N 张照片（调试用，0=全部）")
    ap.add_argument("--order", default="random",
                    choices=["random", "name_asc", "name_desc", "ctime_asc", "ctime_desc"],
                    help="照片顺序：random=随机(默认) / name_asc=文件名升序 / "
                         "name_desc=文件名降序 / ctime_asc=创建时间升序 / "
                         "ctime_desc=创建时间降序")
    ap.add_argument("--music", default=None,
                    help="背景音乐文件（默认: 工作目录 Audio\\ 下已有音频，"
                         "否则从照片应用音乐缓存随机选一首并复制到 Audio\\）")
    ap.add_argument("--music-dir", default=None,
                    help="照片应用音乐缓存目录（默认自动探测 LocalState\\Slideshow\\Music\\Audio）")
    ap.add_argument("--music-style", default=None,
                    help="仅收集指定风格（Beats/Chill/Energetic/Epic/Fun/Sentimental，默认全部）")
    ap.add_argument("--music-track", default=None,
                    help="仅收集指定曲段（Main / Intro，默认全部曲段都收集）")
    ap.add_argument("--fade-sec", type=float, default=2.0,
                    help="结尾音量渐弱时长（秒，默认 2）")
    args = ap.parse_args()

    here = os.path.dirname(os.path.abspath(__file__))
    if args.pic_dir is None:
        args.pic_dir = os.path.join(here, "PIC")
    if args.out is None:
        args.out = os.path.join(here, "照片幻灯片放映.prproj")
    if args.seed is None:
        args.seed = random.randint(0, 2 ** 31 - 1)
    if args.min_dur < 1 or args.max_dur < args.min_dur:
        raise SystemExit("参数错误：1 <= min-dur <= max-dur")

    rng = random.Random(args.seed)
    n, total, n_oid, n_uid, music = build(args, os.path.abspath(args.out),
                                          os.path.abspath(args.pic_dir), rng)
    print(f"已生成: {os.path.abspath(args.out)}")
    print(f"  照片数: {n}")
    print(f"  总时长: {total / SEQ_TB:.1f} 秒 ({total / SEQ_TB / 60:.1f} 分钟)")
    print(f"  随机种子: {args.seed}  |  对象数: {n_oid} (ObjectID) / {n_uid} (ObjectUID)")
    if music is not None:
        n_trk = len(music.tracks)
        print(f"  背景音乐: {n_trk} 段配乐（{music.n_seg} 播放段，结尾渐弱）")
    else:
        print("  背景音乐: 未启用（未找到音乐来源）")
    print("  验证: XML 可解析、无重复 ID、所有引用均能解析 ✔")


if __name__ == "__main__":
    main()
